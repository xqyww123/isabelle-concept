(*  Title:      concept_intro_table.ML

The intro table of concept_fact: its entries and their keys, the form of a concept fact, the
rules that apply to a goal, and the derivations that the search gives.  What fills the table
belongs here too: the attribute concept_intro with strengthening; the declaration of
extraction rules by the attribute concept_extraction; assumption destruction with activation,
for facts with and without premises; the activation list of a concept at its declaration; what
a declaration in a theory stores, for a rule, an instance and an import; the function on the
facts that a context indexes, with the option auto_concept_extraction; the lookup table of the
facts of a context, by which conditions are closed; the handler of simp for the premises that
the simplifier assumes.
*)

(*** The check on a chain of steps ***)

(*What lets assumption destruction end (4A.1 of the plan of defining contexts).  Each node of a
  traversal carries a record of the facts on its chain of steps.  A fact grows from an earlier
  one of its kind when the earlier one is embedded in it and is smaller, or is the same up to
  types and the names of variables.  On a chain only one relation fact may grow, and after the
  last rule only one concept fact; and a relation fact must not contain earlier facts with
  three different groups of arguments*)

signature CONCEPT_CHECK =
sig
  (*what the check reads off the theory and the context where the traversal starts: the
    variables fixed there, the arguments that name a concept, a structure below the constants
    of views at its head, the types of structures*)
  type reading =
   {fixed: string -> bool, concept_name: term -> bool, below_views: term -> term,
    structure_type: typ -> bool}
  type record
  val empty: record
  val after_rule: record -> record
  val same: record * record -> bool
  datatype two_groups = Aside | Refused | Allowed
  datatype reason =
    Grows_Again of {from: term, same: bool, grew: term}
  | Contains of term list
  datatype verdict = Passes of record | Set_Aside | Fails of reason
  val relation_fact: reading -> two_groups -> record -> term -> verdict
  val concept_fact: reading -> record -> string -> term -> term -> verdict
end;

structure Concept_Check: CONCEPT_CHECK =
struct

type reading =
 {fixed: string -> bool, concept_name: term -> bool, below_views: term -> term,
  structure_type: typ -> bool};


(** label trees **)

datatype label = Constant of string | Fixed of string | Variable | Lambda;

datatype tree = Tree of label * tree list;

(*of a term in beta-eta normal form*)
fun tree_of ({fixed, ...}: reading) =
  let
    fun label (Const (c, _)) = Constant c
      | label (Free (x, _)) = if fixed x then Fixed x else Variable
      | label _ = Variable;
    fun tree (Abs (_, _, b)) = Tree (Lambda, [tree b])
      | tree t = let val (h, args) = strip_comb t in Tree (label h, map tree args) end;
  in tree end;

fun size (Tree (_, ts)) = fold (Integer.add o size) ts 1;

(*p is in a child of q; or their labels agree and the children of p are, in their order, in
  some of the children of q*)
fun embedded (p as Tree (a, ps)) (Tree (b, qs)) =
  exists (embedded p) qs orelse (a = b andalso embedded_list ps qs)
and embedded_list [] _ = true
  | embedded_list _ [] = false
  | embedded_list (p :: ps) (q :: qs) =
      (embedded p q andalso embedded_list ps qs) orelse embedded_list (p :: ps) qs;

(*a term without its types, its variables that are not fixed named in the order in which they
  first occur: the same for terms that differ in types and in such names only*)
fun plain ({fixed, ...}: reading) t =
  let
    fun name v names =
      (case AList.lookup (op =) names v of
        SOME i => (i, names)
      | NONE => (length names, (v, length names) :: names));
    fun variable v names =
      let val (i, names') = name v names in (Var (("v", i), dummyT), names') end;
    fun go (Const (c, _)) names = (Const (c, dummyT), names)
      | go (t as Free (x, _)) names =
          if fixed x then (Free (x, dummyT), names) else variable t names
      | go (t as Var _) names = variable t names
      | go (Bound i) names = (Bound i, names)
      | go (Abs (_, _, b)) names =
          let val (b', names') = go b names in (Abs ("", dummyT, b'), names') end
      | go (t $ u) names =
          let
            val (t', names') = go t names;
            val (u', names'') = go u names';
          in (t' $ u', names'') end;
  in #1 (go (Term.map_types (K dummyT) t) []) end;


(** what a fact is to the check **)

datatype category = Structure | Other of typ;

(*an argument of a relation fact that names no concept, below the views at its head*)
type argument = {tree: tree, category: category};

(*group: the arguments as one term in plain form: the same for two groups of arguments that
  differ in types and in the names of variables only*)
type item =
 {prop: term, tree: tree, plain: term, arguments: argument list, group: term};

fun item_of (reading as {concept_name, below_views, structure_type, ...}: reading) relation A =
  let
    val args =
      if relation then map below_views (filter_out concept_name (#2 (strip_comb A))) else [];
    fun argument u =
      {tree = tree_of reading u,
       category = if structure_type (fastype_of u) then Structure else Other (fastype_of u)};
  in
    {prop = A, tree = tree_of reading A, plain = plain reading A, arguments = map argument args,
     group = plain reading (Term.list_comb (Const ("", dummyT), args))}: item
  end;

(*q grows from p, a fact of its kind*)
fun grows_from (q: item) (p: item) =
  embedded (#tree p) (#tree q) andalso
    (size (#tree p) < size (#tree q) orelse #plain p aconv #plain q);

(*the arguments of p, at least one, are embedded in some of the arguments of q, each in one of
  its category and in their order, and are smaller together*)
fun arguments_embedded (ps: argument list) (qs: argument list) =
  let
    fun embedded_in [] _ = true
      | embedded_in _ [] = false
      | embedded_in (p :: ps') (q :: qs') =
          (#category p = #category q andalso embedded (#tree p) (#tree q) andalso
            embedded_in ps' qs') orelse embedded_in (p :: ps') qs';
    val total = fold (Integer.add o size o #tree);
  in not (null ps) andalso embedded_in ps qs andalso total ps 0 < total qs 0 end;


(** records **)

(*the facts of one part by their kinds, and the one of them that has grown*)
type part = {items: item list Symtab.table, grown: term option};

val empty_part: part = {items = Symtab.empty, grown = NONE};

(*relations: the relation facts of the whole chain; concepts: the concept facts since the last
  rule*)
type record = {relations: part, concepts: part};

val empty: record = {relations = empty_part, concepts = empty_part};

fun after_rule ({relations, ...}: record) : record =
  {relations = relations, concepts = empty_part};

(*the same facts in the same order, and the same one grown*)
fun same (r: record, r': record) =
  let
    fun same_part ({items, grown}: part, {items = items', grown = grown'}: part) =
      eq_option (op aconv) (grown, grown') andalso
      eq_list (eq_pair (op =) (eq_list (op aconv o apply2 #prop)))
        (Symtab.dest items, Symtab.dest items');
  in
    same_part (#relations r, #relations r') andalso same_part (#concepts r, #concepts r')
  end;

fun of_kind ({items, ...}: part) kind = Symtab.lookup_list items kind;

fun add kind (item: item) grew ({items, grown}: part) : part =
  {items = Symtab.cons_list (kind, item) items,
   grown = if is_none grown andalso grew then SOME (#prop item) else grown};


(** the check **)

(*what is done with a relation fact that contains earlier facts with two different groups of
  arguments: it waits for the second pass, it fails, or it passes*)
datatype two_groups = Aside | Refused | Allowed;

(*why a fact fails: it grows from an earlier fact of its kind, the same up to types and the
  names of variables or smaller, while a fact of its part has grown; or it contains these
  earlier facts, whose groups of arguments differ*)
datatype reason =
  Grows_Again of {from: term, same: bool, grew: term}
| Contains of term list;

(*Passes: the record with the fact added*)
datatype verdict = Passes of record | Set_Aside | Fails of reason;

(*a fact of a part that grows from p although a fact of the part has grown*)
fun grows_again (q: item) (p: item) grew =
  Grows_Again {from = #prop p, same = #plain p aconv #plain q, grew = grew};

(*A relation fact R u1 ... um, without Trueprop, in beta-eta normal form.  Its sources are the
  facts of its relation that it grows from, and the facts of other relations whose arguments
  are embedded in its own*)
fun relation_fact reading two_groups ({relations, concepts}: record) A =
  let
    val R = (case Term.head_of A of Const (c, _) => c | _ => raise TERM ("relation_fact", [A]));
    val q = item_of reading true A;
    val grown_from = filter (grows_from q) (of_kind relations R);
    val others =
      Symtab.fold (fn (R', ps) => R' <> R ? append ps) (#items relations) []
      |> filter (fn p => arguments_embedded (#arguments p) (#arguments q));
    (*one source of each group of arguments*)
    val sources = distinct (op aconv o apply2 #group) (grown_from @ others);
    fun passes () =
      Passes {relations = add R q (not (null grown_from)) relations, concepts = concepts};
  in
    (case (grown_from, #grown relations) of
      (p :: _, SOME grew) => Fails (grows_again q p grew)
    | _ =>
        (case (length sources, two_groups) of
          (0, _) => passes ()
        | (1, _) => passes ()
        | (2, Allowed) => passes ()
        | (2, Aside) => Set_Aside
        | _ => Fails (Contains (map #prop sources))))
  end;

(*A concept fact C t in its form, without Trueprop, with the structure u of t below its
  truncations; its kind is C with the head of u*)
fun concept_fact (reading as {fixed, ...}: reading) ({relations, concepts}: record) C u A =
  let
    val head =
      (case Term.head_of u of
        Const (c, _) => c
      | Free (x, _) => if fixed x then ":" ^ x else ""
      | _ => "");
    val kind = C ^ " " ^ head;
    val q = item_of reading false A;
    val grown_from = filter (grows_from q) (of_kind concepts kind);
  in
    (case (grown_from, #grown concepts) of
      (p :: _, SOME grew) => Fails (grows_again q p grew)
    | _ => Passes {relations = relations, concepts = add kind q (not (null grown_from)) concepts})
  end;

end;



(*** The intro table ***)

signature CONCEPT_INTRO_TABLE =
sig
  datatype safety = Unsafe | Safe_By_User | Safe_By_System
  type entry = {concept: string, rule: thm, user: bool, safety: safety, pos: Position.T}
  val dest_fact: theory -> term -> (string * string * term) option
  val is_concept_premise: theory -> term -> bool
  val canonical: term -> term
  type form
  val form_of_goal: Proof.context -> term -> form option
  val form_prop: form -> term
  val form_equation: form -> thm lazy option
  val entries_for: Proof.context -> form -> entry list
  datatype how_matched = As_Written | Converted of {extra: bool, reached: bool}
  type matched =
   {premises: term list, rule: thm lazy, concept_distance: int, how: how_matched}
  val match_rule: Proof.context -> entry -> form -> matched option
  type equation = thm lazy
  datatype derivation =
    Goal of {goal: term, form: equation option, solutions: solution list}
  and solution =
    Solution of
     {entry: entry option, rule: thm lazy, converted: bool, premises: premise list}
  and premise =
      Concept of
       {params: (string * (string * typ)) list, hyps: term list, derivation: derivation}
    | Remaining of {cond: term, simp: equation option}
  val derivation_terms: derivation -> term list
  val shown_condition: {cond: term, simp: equation option} -> term
  val formula_of: term -> term
  val formula_conv: Proof.context -> conv
  val conditions_of: derivation -> term
  val under: {params: (string * (string * typ)) list, hyps: term list} -> term -> term
  val map_derivation: (term -> term) -> (thm -> thm) -> derivation -> derivation
  val goal_thm: Proof.context -> derivation -> thm -> thm
  datatype failure = No_Plan | User_Limit | Not_Concept_Goal
  datatype 'a result = Found of {value: 'a, cut_short: bool} | Failed of failure
  type destruct_work = {safe_intro: bool, notation: bool, masked_entries: bool}
  datatype site = In_Context | Internal_Call | Host_Premise | Theory_Level
  val destruct_assms: destruct_work -> site -> thm list -> Proof.context -> Proof.context
  val activation_list: theory -> string -> thm list
  val destruction_state: Proof.context ->
    {capped: (term * int) list, stopped: (term * term list) list}
  val mark_handled: thm -> thm
  val extraction_limit: int Config.T
  val extraction_trace: bool Config.T
  val fact_context: Proof.context -> thm -> thm * Proof.context
  val add_instance_entries: {rule: thm, theorem: thm} -> theory -> theory
  val add_system_entries: {rule: thm, safety: safety option} list -> theory -> theory
  val has_work: theory -> term -> bool  (*for tests*)
  val auto_extraction: bool Config.T
  val concept_extract: Proof.context -> Proof.context
  val lookup_fact: Proof.context -> term -> thm option
  val lookup_table: Proof.context -> thm list  (*for tests*)
end;

(*the form of a concept fact, sealed inside Concept_Intro_Table*)
signature CONCEPT_FORM =
sig
  type form
  val concept: form -> string
  val structure_term: form -> term
  val inner: form -> term
  val prop: form -> term
  val equation: form -> thm lazy option
  val of_goal: Proof.context -> term -> form option
  type fact
  val of_thm: Proof.context -> thm -> fact option
  val thm_of: fact -> thm
  val conclusion: fact -> form
  val base_thm: Proof.context -> fact -> thm
end;

structure Concept_Intro_Table: CONCEPT_INTRO_TABLE =
struct

(** entries **)

datatype safety = Unsafe | Safe_By_User | Safe_By_System;

(*an entry as it is handed out, with the theorem that holds where it is asked for.  It has no
  name: what refers to a concept fact gives its proposition.  pos: where a user declared the
  rule, none for an entry that the system makes*)
type entry = {concept: string, rule: thm, user: bool, safety: safety, pos: Position.T};

fun map_entry_rule f ({concept, rule, user, safety, pos}: entry) : entry =
  {concept = concept, rule = f rule, user = user, safety = safety, pos = pos};



(** concept facts **)

(*the concept of a proposition C t, the constant of its predicate, and t*)
fun dest_fact thy (\<^Const_>\<open>Trueprop for \<open>Const (c, _) $ t\<close>\<close>) =
      Concept.concept_of_predicate thy c |> Option.map (fn C => (C, c, t))
  | dest_fact _ _ = NONE;

(*A premise !!xs. H1 ==> ... ==> Hn ==> C t is a concept premise unless some Hi concludes a
  concept fact in turn (4.1 of the search plan)*)
fun is_concept_premise thy prem =
  let val concludes_fact = is_some o dest_fact thy o Logic.strip_assums_concl in
    concludes_fact prem andalso not (exists concludes_fact (Logic.strip_assums_hyp prem))
  end;

(*a structure term below the truncations at its head*)
fun below thy t =
  (case Concept_Type.dest_truncation thy t of SOME (_, u) => below thy u | NONE => t);



(** the form of a concept fact **)

(*The form of C t (3.1 of the search plan): t in beta-eta normal form, rewritten by the selector
  Simpset, then the truncations at its head dropped as long as the predicate lets them go.
  Whatever tests, keys, compares or stores a concept fact takes a value made here*)

structure Form :> CONCEPT_FORM =
struct

(*inner: the structure term below all truncations at its head, whatever the predicate;
  equation: C t == the form for a goal, where the two differ; none in the conclusion of a fact*)
datatype form = Form of
 {concept: string, structure_term: term, inner: term, prop: term, equation: thm lazy option};

fun concept (Form {concept, ...}) = concept;
fun structure_term (Form {structure_term, ...}) = structure_term;
fun inner (Form {inner, ...}) = inner;
fun prop (Form {prop, ...}) = prop;
fun equation (Form {equation, ...}) = equation;

(*no schematic variables*)
fun fixed_form ctxt (C, c, t) =
  let
    val thy = Proof_Context.theory_of ctxt;
    (*the steps on the structure term, each t1 == t2, none where it changes nothing*)
    fun normal t1 =
      if Envir.beta_eta_contract t1 aconv t1 then NONE
      else SOME (Drule.beta_eta_conversion (Thm.cterm_of ctxt t1));
    fun simp t1 =
      if Concept_Type.may_rewrite ctxt t1 then
        let val eq = Concept_Type.selector_conv ctxt (Thm.cterm_of ctxt t1)
        in if Thm.is_reflexive eq then NONE else SOME eq end
      else NONE;
    fun step f (t1, eqs) =
      (case f t1 of SOME eq => (Thm.term_of (Thm.rhs_of eq), eq :: eqs) | NONE => (t1, eqs));
    val (t', rewrites) = (t, []) |> step normal |> step simp |> step normal;
    fun strip t1 eqs =
      (case Concept_Package.truncation_equation ctxt c t1 of
        SOME eq => strip (#2 (the (Concept_Type.dest_truncation thy t1))) (eq :: eqs)
      | NONE => (t1, eqs));
    val (t'', strips) = strip t' [];
    val steps =
      map (Drule.arg_cong_rule (Thm.cterm_of ctxt (Term.head_of (Concept_Package.holds c t))))
        (rev rewrites) @
      map (fn eq => eq RS @{thm eq_reflection}) (rev strips);
  in
    Form
     {concept = C, structure_term = t'', inner = below thy t'',
      prop = HOLogic.mk_Trueprop (Concept_Package.holds c t''),
      equation =
        if null steps then NONE
        else
          SOME (Lazy.value
            (Drule.arg_cong_rule \<^cterm>\<open>Trueprop\<close> (foldl1 (uncurry Thm.transitive) steps)))}
  end;

fun of_goal ctxt goal =
  dest_fact (Proof_Context.theory_of ctxt) goal |> Option.map (fn (C, c, t) =>
    if Term.maxidx_of_term goal = ~1 then fixed_form ctxt (C, c, t)
    else
      let
        val {context, fix, thaw, thaw_thm, ...} = Concept_Type.fix_schematics ctxt [goal];
        val Form {structure_term, inner, prop, equation, ...} = fixed_form context (C, c, fix t);
      in
        Form
         {concept = C, structure_term = thaw structure_term, inner = thaw inner,
          prop = thaw prop, equation = Option.map (Lazy.map thaw_thm) equation}
      end);

(*a theorem ... ==> C t in beta-eta normal form, with its conclusion in the form, and each
  premise that concludes a concept fact; its schematic variables have index 0*)
datatype fact = Fact of {thm: thm, conclusion: form};

fun thm_of (Fact {thm, ...}) = thm;
fun conclusion (Fact {conclusion, ...}) = conclusion;

fun of_thm ctxt th0 =
  let
    val thy = Proof_Context.theory_of ctxt;
    val th = Conv.fconv_rule Drule.beta_eta_conversion th0;
  in
    if is_none (dest_fact thy (Thm.concl_of th)) then NONE
    else
      let
        fun fact_conv ctxt' ct =
          (case Option.map (fixed_form ctxt') (dest_fact thy (Thm.term_of ct)) of
            SOME (Form {equation = SOME eq, ...}) => Lazy.force eq
          | _ => Thm.reflexive ct);
        fun prem_conv ctxt' = Conv.params_conv ~1 (Conv.concl_conv ~1 o fact_conv) ctxt';
        val th' =
          Concept_Type.fixing ctxt (Thm.prop_of th :: Thm.hyps_of th)
            (fn ctxt' => fn freeze => fn _ =>
              Conv.fconv_rule
                (Conv.prems_conv ~1 (prem_conv ctxt') then_conv
                  Conv.concl_conv ~1 (fact_conv ctxt'))
                (freeze th))
          |> Drule.zero_var_indexes;
        val (C, _, t) = the (dest_fact thy (Thm.concl_of th'));
      in
        SOME (Fact
         {thm = th',
          conclusion =
            Form
             {concept = C, structure_term = t, inner = below thy t, prop = Thm.concl_of th',
              equation = NONE}})
      end
  end;

(*... ==> concept u for a fact ... ==> C t, u being t below the truncations at its head: every
  concept gives the base concept, below which every truncation goes*)
fun base_thm ctxt (Fact {thm, conclusion = Form {concept = C, ...}, ...}) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val base = Concept_Type.base_name thy;
  in
    if C = base then thm
    else
      thm RS #entailment (the (Concept_Package.entailment thy C base))
      |> of_thm ctxt |> the |> thm_of
  end;

end;

type form = Form.form;
val form_of_goal = Form.of_goal;
val form_prop = Form.prop;
val form_equation = Form.equation;



(** the table **)

(* keys *)

(*The key of an entry and of a goal is read off the structure term below its truncations: that
  of the type layer, which links keys, where the head is a constant; a variable of the context;
  one key for all structures with a schematic variable at the head.  No constant has a name
  like the last two*)

val schematic_key = "?";

fun key_of thy t =
  (case Concept_Type.key_of thy t of
    SOME key => key
  | NONE => (case Term.head_of (below thy t) of Free (x, _) => ":" ^ x | _ => schematic_key));

(*the schematic variable at the head of the structure of a form, below its truncations: such a
  structure is any structure*)
fun schematic_head form =
  (case Term.head_of (Form.inner form) of head as Var _ => SOME head | _ => NONE);


(* entries of one proposition *)

(*a term with its schematic variables named in the order in which they first occur: the same
  for terms that differ in the names of schematic variables only*)
fun canonical t =
  if Term.maxidx_of_term t = ~1 then t
  else
    let
      val instT =
        TVars.make (map_index (fn (i, v as (_, S)) => (v, TVar (("'a", i), S)))
          (rev (Term.add_tvars t [])));
      val t' = Term_Subst.instantiate (instT, Vars.empty) t;
      val inst =
        Vars.make (map_index (fn (i, v as (_, T)) => (v, Var (("x", i), T)))
          (rev (Term.add_vars t' [])));
    in Term_Subst.instantiate (TVars.empty, inst) t' end;

fun stronger (Safe_By_System, _) = Safe_By_System
  | stronger (_, Safe_By_System) = Safe_By_System
  | stronger (Safe_By_User, _) = Safe_By_User
  | stronger (_, safety) = safety;

(*What a part of the table has for one proposition, and what the set says of a key: one value
  usable everywhere, or one for each premise of the simplifier that gave it, with the mask of
  that premise, in the order they came; never both.  A value is added only where none serves
  the call, so masks are never compared.  That a masked value is used only where it holds, and
  wherever it holds, rests on the simplifier: a premise in force stays in force below*)
datatype 'a masked = Unmasked of 'a | Masked of ('a * (Proof.context -> bool)) list;

fun map_masked f (Unmasked a) = Unmasked (f a)
  | map_masked f (Masked alts) = Masked (map (apfst f) alts);

fun usable _ (Unmasked a) = SOME a
  | usable ctxt (Masked alts) = Option.map #1 (find_first (fn (_, mask) => mask ctxt) alts);

(*a value usable wherever what a call with this mask writes is used.  A masked call runs where
  its premise is in force (destruct_facts): a masked value usable there is usable wherever
  that premise is*)
fun serving ctxt mask m =
  (case (mask, m) of
    (_, Unmasked a) => SOME a
  | (NONE, Masked _) => NONE
  | (SOME _, _) => usable ctxt m);

fun add_masked (NONE, a) _ = Unmasked a
  | add_masked (SOME mask, a) NONE = Masked [(a, mask)]
  | add_masked (SOME mask, a) (SOME (Masked alts)) = Masked (alts @ [(a, mask)])
  | add_masked (SOME _, _) (SOME m) = m;

(*the mask of what a masked call writes for the theorem th0 that the handler of simp got*)
fun mask_of th0 ctxt = Raw_Simplifier.simproc_can_use_thm ctxt th0;

(*an entry as the table keeps it*)
type stored = {concept: string, rules: thm masked, user: bool, safety: safety, pos: Position.T};

fun first_rule ({rules, ...}: stored) =
  (case rules of Unmasked th => th | Masked alts => #1 (hd alts));

fun map_rules f ({concept, rules, user, safety, pos}: stored) : stored =
  {concept = concept, rules = map_masked f rules, user = user, safety = safety, pos = pos};

fun with_mark safety ({concept, rules, user, safety = safety', pos}: stored) : stored =
  {concept = concept, rules = rules, user = user, safety = stronger (safety, safety'), pos = pos};

(*of two entries of one proposition one stays: one without a mask, then one of a user, then the
  lesser theorem; two with masks keep the theorems of both, those of the first one first.  It
  gets the stronger mark of the two*)
fun join_entries (s: stored, s': stored) : stored =
  let
    fun rank ({rules, user, ...}: stored) =
      (case rules of Unmasked _ => false | Masked _ => true, not user);
    val ord = prod_ord bool_ord bool_ord o apply2 rank ||| Thm.thm_ord o apply2 first_rule;
    val {concept, rules, user, pos, ...} = if ord (s, s') = GREATER then s' else s;
    val rules' =
      (case (#rules s, #rules s') of
        (Masked alts, Masked alts') => Masked (alts @ alts')
      | _ => rules);
  in
    {concept = concept, rules = rules', user = user, safety = stronger (#safety s, #safety s'),
     pos = pos}
  end;

(*the entries of a key, each by its proposition with canonical variables: one entry of one
  proposition*)
type table = stored Termtab.table Symtab.table;

fun entries_of (tab: table) key = the_default Termtab.empty (Symtab.lookup tab key);


(* registration *)

(*what goes into the table is a fact in its form: the key and the proposition of the entry are
  read off it*)
type registration =
 {fact: Form.fact, user: bool, safety: safety, mask: (Proof.context -> bool) option,
  pos: Position.T};

(*the proposition by which the table tells the entry of a fact from its other entries*)
fun entry_prop fact = canonical (Thm.prop_of (Form.thm_of fact));

local

(*the two parts of the table: nothing outside this block writes them*)
structure Static = Theory_Data
(
  type T = table;
  val empty = Symtab.empty;
  val merge = Symtab.join (K (Termtab.join (K join_entries)));
);

structure Contextual = Proof_Data
(
  type T = table;
  fun init _ = Symtab.empty;
);

fun entry_of ({fact, user, safety, mask, pos}: registration) : stored =
  {concept = Form.concept (Form.conclusion fact),
   rules = add_masked (mask, Form.thm_of fact) NONE, user = user, safety = safety, pos = pos};

fun place thy ({fact, ...}: registration) =
  (key_of thy (Form.inner (Form.conclusion fact)), entry_prop fact);

fun insert (key, prop) (e: stored) (tab: table) =
  Symtab.update (key,
    Termtab.map_default (prop, e) (fn e' => join_entries (e', e)) (entries_of tab key)) tab;

in

(*The only writer of the part of the theory.  made gets the theory before anything of this
  registration is in it; what it gives goes in at once, so no entry of a registration can hide
  the activation of another*)
fun register_theory (made: theory -> registration list) thy =
  Static.put
    (fold (fn r => insert (place thy r) (map_rules Thm.trim_context (entry_of r)))
      (made thy) (Static.get thy))
    thy;

(*whether the proposition is new to the table.  Nothing is written where the static part has
  the entry with a mark at least as strong: the contextual part stays small.  Where an entry
  serves the call, a masked registration only gives it its mark*)
fun add_contextual (r: registration) ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (key, prop) = place thy r;
    val static = Termtab.lookup (entries_of (Static.get thy) key) prop;
    val tab = Contextual.get ctxt;
    val covered =
      (case static of
        SOME e => stronger (#safety e, #safety r) = #safety e
      | NONE => false);
    val served =
      (case Termtab.lookup (entries_of tab key) prop of
        SOME s => is_some (serving ctxt (#mask r) (#rules s))
      | NONE => false);
  in
    if covered then (false, ctxt)
    else
      (is_none static andalso not served,
       Contextual.put
        (if served andalso is_some (#mask r)
         then Symtab.map_entry key (Termtab.map_entry prop (with_mark (#safety r))) tab
         else insert (key, prop) (entry_of r) tab) ctxt)
  end;

(*the contextual part as a whole: a fact that the limit has cut is taken apart again on what
  its context had before (4A.5 of the plan of defining contexts)*)
val contextual_part = Contextual.get;
val put_contextual_part = Contextual.put;

(*those under the key of the goal, under the keys linked to it, under the key of the parameter
  that "where super = ..." names, and the facts on schematic structures; an entry that
  premises of the simplifier gave has the first of their theorems that holds now, and is left
  out where none does; an entry of each part for one proposition joined into one; in the order
  of their theorems*)
fun entries_for ctxt form =
  let
    val thy = Proof_Context.theory_of ctxt;
    val u = Form.inner form;
    val key = key_of thy u;
    val super =
      (case strip_comb u of
        (Const (c, _), args) =>
          (case Concept_Type.super_param thy c of
            SOME i => if i < length args then [key_of thy (nth args i)] else []
          | NONE => [])
      | _ => []);
    val keys = distinct (op =) (key :: Concept_Type.linked_keys thy key @ super @ [schematic_key]);
    fun now (es: stored Termtab.table) =
      Termtab.fold (fn (prop, s: stored) =>
        (case #rules s of
          Unmasked _ => I
        | Masked alts =>
            (case find_first (fn (_, mask) => mask ctxt) alts of
              SOME alt =>
                Termtab.update (prop,
                  {concept = #concept s, rules = Masked [alt], user = #user s,
                   safety = #safety s, pos = #pos s})
            | NONE => Termtab.delete prop))) es es;
    fun handed_out (s: stored) : entry =
      {concept = #concept s, rule = first_rule s, user = #user s, safety = #safety s, pos = #pos s};
    val static = Static.get thy and contextual = Contextual.get ctxt;
  in
    keys |> maps (fn key =>
      (entries_of static key, now (entries_of contextual key))
      |> Termtab.join (K join_entries)
      |> Termtab.dest |> map (handed_out o #2))
    |> map (map_entry_rule (Thm.transfer' ctxt))
    |> sort (Thm.thm_ord o apply2 #rule)
  end;

end;



(** matching a rule against a goal **)

datatype how_matched = As_Written | Converted of {extra: bool, reached: bool};

type matched =
 {premises: term list, rule: thm lazy, concept_distance: int, how: how_matched};

fun fresh_index maxidx =
  let val i = serial () in if i > maxidx then i else fresh_index maxidx end;

(*the concept distance of a rule of the concept N on a goal C t, where the table of entailments
  says distance (4.2 of the search plan): on a structure made by an instance declared as D, the
  layers from D to its ancestors do not count*)
fun concept_distance thy N (C, t) distance =
  (case Term.head_of t of
    Const (c, _) =>
      (case Concept_Type.get_instance thy c of
        SOME {concept = (_, D), ...} =>
          if C <> D andalso is_none (Concept_Package.entailment thy D C) then distance
          else if N = D then 0
          else
            (case Concept_Package.entailment thy N D of
              SOME {distance = d, ...} => d
            | NONE => if is_some (Concept_Package.entailment thy D N) then 0 else distance)
      | NONE => distance)
  | _ => distance);

(*a matcher as an instantiation*)
fun instantiation (tyenv, tenv) =
  (TVars.build (tyenv |> Vartab.fold (fn (ai, (S, T)) => TVars.add ((ai, S), T))),
   Vars.build (tenv |> Vartab.fold (fn (xi, (T, t)) =>
    Vars.add ((xi, Envir.subst_type tyenv T), t))));

(*a theorem under a matcher, in beta-eta normal form*)
fun instance_of ctxt env th =
  let val (instT, inst) = instantiation env in
    th
    |> Thm.instantiate
        (TVars.map (K (Thm.ctyp_of ctxt)) instT, Vars.map (K (Thm.cterm_of ctxt)) inst)
    |> Conv.fconv_rule Drule.beta_eta_conversion
  end;

(*A rule ... ==> N s on a goal C t, N being C or below it.  First s is matched against t as
  written; else the type layer makes the truncations of the two equal (3.2 of the search plan),
  which takes that the truncation goes below C on both sides.  The schematic variables of the
  goal stay.  Those of the rule have index 0; the ones that the match leaves get an index that
  no other call gives*)
fun match_rule ctxt ({concept = N, rule, pos, ...}: entry) form =
  let
    val thy = Proof_Context.theory_of ctxt;
    val C = Form.concept form;
    val t = Form.structure_term form;
    val goal = Form.prop form;
    val (_, c, _) = the (dest_fact thy goal);
    val i = fresh_index (Term.maxidx_of_term goal);
    val shift = Logic.incr_indexes ([], i);
    val (_, n, s) = the (dest_fact thy (shift (Thm.concl_of rule)));
    val base = Concept_Type.base_name thy;

    (*under the trace, a rule of a concept that gives that of the goal says why it does not
      apply; a rule of another concept is passed over in silence*)
    fun dropped reason =
      (if Config.get ctxt Concept_Type.trace then
        tracing ("concept_fact: the rule " ^ Thm.string_of_thm ctxt rule ^ Position.here pos ^
          " does not apply to " ^ Syntax.string_of_term ctxt goal ^ ": " ^ reason)
       else ();
       NONE);

    (*the instance of the rule under a matcher of s, in beta-eta normal form like the form of
      the goal and the premises handed back*)
    fun instance env = instance_of ctxt env (Thm.incr_indexes i rule);
    fun instantiated env =
      Envir.beta_eta_contract o Term_Subst.instantiate (instantiation env) o shift;
  in
    (case
      if N = C then SOME NONE else Option.map SOME (Concept_Package.entailment thy N C)
     of
      NONE => NONE
    | SOME up =>
        let
          val distance =
            concept_distance thy N (C, t) (case up of SOME {distance, ...} => distance | NONE => 0);
          (*N u ==> C u*)
          fun entail th =
            (case up of SOME {entailment, ...} => th RS entailment | NONE => th);
          fun result how premises derive =
            if exists (fn prem => prem aconv goal) premises then
              dropped "one of its premises is the goal"
            else
              SOME
               {premises = premises, rule = Lazy.lazy derive, concept_distance = distance,
                how = how};
        in
          (case try (Pattern.match thy (s, t)) (Vartab.empty, Vartab.empty) of
            SOME env =>
              let val premises = map (instantiated env) (Thm.prems_of rule) in
                result As_Written premises (fn () =>
                  if is_none up then instance env
                  else
                    Concept_Type.fixing ctxt (goal :: premises) (fn _ => fn freeze => fn _ =>
                      entail (freeze (instance env))))
              end
          | NONE =>
              if C = base then dropped "its structure does not match that of the goal"
              else
                (case Concept_Type.truncate_eq ctxt {concept = C, s = s, t = t} of
                  NONE =>
                    dropped
                      "its structure does not match that of the goal, and their truncations \
                      \are not made equal"
                | SOME {env, eq, extra, reached} =>
                    let
                      val s' = instantiated env (Thm.concl_of rule) |> dest_fact thy |> the |> #3;
                      val truncated =
                        Concept_Type.mk_truncate thy (#owner (Concept_Type.the_info thy C));
                      val goes =
                        let val {context, fix, ...} = Concept_Type.fix_schematics ctxt [s', t] in
                          [s', t] |> forall (fn u =>
                            is_some
                              (Concept_Package.truncation_equation context c (truncated (fix u))))
                        end;
                      val premises =
                        map (instantiated env) (Thm.prems_of rule) @
                        the_list
                          (Option.map (HOLogic.mk_Trueprop o Concept_Package.holds base) extra);
                      (*N s' ==> (concept t ==>) C t, then the rule put in front of it*)
                      fun derive () =
                        Concept_Type.fixing ctxt (goal :: s' :: premises)
                         (fn ctxt' => fn freeze => fn fix =>
                          let
                            val s1 = fix s' and t1 = fix t;
                            val cprop = Thm.cterm_of ctxt' o HOLogic.mk_Trueprop;
                            val assumed = Thm.assume (cprop (Concept_Package.holds n s1));
                            val to_base =
                              #entailment (the (Concept_Package.entailment thy N base));
                            val needs =
                              map (cprop o Concept_Package.holds base o fix) (the_list extra);
                            val truncations_eq =
                              Drule.implies_elim_list (freeze (Lazy.force eq))
                                ((assumed RS to_base) :: map Thm.assume needs);
                            val goes_at =
                              the o Concept_Package.truncation_equation ctxt' c o truncated;
                            val converted =
                              (@{thm iffD2} OF [goes_at s1, entail assumed])
                              |> Thm.equal_elim
                                  (Drule.arg_cong_rule \<^cterm>\<open>Trueprop\<close>
                                    (Drule.arg_cong_rule
                                      (Thm.cterm_of ctxt'
                                        (Term.head_of (Concept_Package.holds c (truncated s1))))
                                      (truncations_eq RS @{thm eq_reflection})))
                              |> (fn th => @{thm iffD1} OF [goes_at t1, th])
                              |> fold_rev Thm.implies_intr needs
                              |> Thm.implies_intr (Thm.cprop_of assumed);
                          in freeze (instance env) RS converted end);
                    in
                      if goes then
                        result (Converted {extra = is_some extra, reached = reached}) premises
                          derive
                      else dropped "a truncation does not go below the concept of the goal"
                    end))
        end)
  end;



(** derivations **)

type equation = thm lazy;

(*a solution without an entry: its rule is a theorem that another search of the same call has
  proved without conditions; it states the form of the goal and has no premise.  A parameter
  of a premise: the name that its binder has in the rule, and the free variable that stands
  for it in the hypotheses and below*)
datatype derivation =
  Goal of {goal: term, form: equation option, solutions: solution list}
and solution =
  Solution of
   {entry: entry option, rule: thm lazy, converted: bool, premises: premise list}
and premise =
    Concept of
       {params: (string * (string * typ)) list, hyps: term list, derivation: derivation}
  | Remaining of {cond: term, simp: equation option};

(*every term that a derivation speaks of, the parameters of its wrappers among them: with their
  schematic variables fixed, nothing in it has one*)
fun derivation_terms (Goal {goal, form, solutions}) =
  goal :: map (Thm.prop_of o Lazy.force) (the_list form) @
  maps (fn Solution {entry = _, rule, converted = _, premises} =>
    Thm.prop_of (Lazy.force rule) ::
    maps
      (fn Concept {params, hyps, derivation} =>
            map (Free o #2) params @ hyps @ derivation_terms derivation
        | Remaining {cond, simp} =>
            cond :: map (Thm.prop_of o Lazy.force) (the_list simp)) premises) solutions;

(*a condition as it is given to the user: what the selector Simpset made of it, where that is
  another proposition*)
fun shown_condition {cond, simp: equation option} =
  (case simp of
    SOME eq => #2 (Logic.dest_equals (Thm.prop_of (Lazy.force eq)))
  | NONE => cond);

(*a proposition as a formula: !! and ==> become ALL and -->*)
fun formula_of (\<^Const_>\<open>Trueprop for A\<close>) = A
  | formula_of (\<^Const_>\<open>Pure.imp for A B\<close>) = HOLogic.mk_imp (formula_of A, formula_of B)
  | formula_of (\<^Const_>\<open>Pure.all T for \<open>Abs (x, _, A)\<close>\<close>) =
      HOLogic.all_const T $ Abs (x, T, formula_of A)
  | formula_of (\<^Const_>\<open>Pure.all T for A\<close>) =
      HOLogic.all_const T $ Abs ("x", T, formula_of (Term.incr_boundvars 1 A $ Bound 0))
  | formula_of (\<^Const_>\<open>Pure.eq T for A B\<close>) = HOLogic.eq_const T $ A $ B
  | formula_of A = raise TERM ("formula_of", [A]);

(*A == Trueprop (formula_of A), for A in beta normal form with every !! on an abstraction*)
fun formula_conv ctxt ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>Trueprop for _\<close> => Conv.all_conv ct
  | \<^Const_>\<open>Pure.imp for _ _\<close> =>
      (Conv.combination_conv (Conv.arg_conv (formula_conv ctxt)) (formula_conv ctxt) then_conv
        Conv.rewr_conv @{thm atomize_imp}) ct
  | \<^Const_>\<open>Pure.all _ for \<open>Abs _\<close>\<close> =>
      (Conv.arg_conv (Conv.abs_conv (formula_conv o #2) ctxt) then_conv
        Conv.rewr_conv @{thm atomize_all}) ct
  | \<^Const_>\<open>Pure.eq _ for _ _\<close> => Conv.rewr_conv @{thm atomize_eq} ct
  | _ => raise CTERM ("formula_conv", [ct]));

(*the conditions that a derivation leaves, as one formula: the solutions of a goal are
  alternatives, the premises of a solution hold together; a condition is in the shape given to
  the user*)
fun conditions_of (Goal {solutions, ...}) =
  foldr1 HOLogic.mk_disj (map (fn Solution {premises, ...} =>
    if null premises then \<^Const>\<open>True\<close>
    else foldr1 HOLogic.mk_conj (map premise_conditions premises)) solutions)
and premise_conditions (Concept {params, hyps, derivation}) =
      conditions_of derivation
      |> fold_rev (fn hyp => fn A => HOLogic.mk_imp (formula_of hyp, A)) hyps
      |> fold_rev (fn (_, (x, T)) => fn A => HOLogic.mk_all (x, T, A)) params
  | premise_conditions (Remaining condition) = formula_of (shown_condition condition);

(*a proposition under the parameters and the hypotheses of a premise again: each parameter is
  bound under the name that its binder has in the rule*)
fun under {params, hyps} prop =
  Logic.list_implies (hyps, prop) |> fold_rev (fn (x, v) => Logic.all_name (x, Free v)) params;


(* the terms and theorems of a derivation *)

fun map_derivation (f: term -> term) (g: thm -> thm) =
  let
    val eq = Option.map (Lazy.map g);
    fun goal (Goal {goal = A, form, solutions}) =
      Goal {goal = f A, form = eq form, solutions = map solution solutions}
    and solution (Solution {entry, rule, converted, premises}) =
      Solution
       {entry = entry, rule = Lazy.map g rule, converted = converted,
        premises = map premise premises}
    and premise (Concept {params, hyps, derivation}) =
          Concept
           {params = map (apsnd (dest_Free o f o Free)) params, hyps = map f hyps,
            derivation = goal derivation}
      | premise (Remaining {cond, simp}) =
          Remaining {cond = f cond, simp = eq simp};
  in goal end;


(* from the conditions to the goal *)

(*A from Trueprop (formula_of A)*)
fun prop_of_formula ctxt A th =
  Thm.equal_elim (Thm.symmetric (formula_conv ctxt (Thm.cterm_of ctxt A))) th;

(*the theorems of A1 ... An from that of A1 & (A2 & ... An), n > 0*)
fun conjuncts 1 th = [th]
  | conjuncts n th =
      let val (th1, th2) = HOLogic.conj_elim th in th1 :: conjuncts (n - 1) th2 end;

(*The goal of a derivation without schematic variables, from a theorem of its conditions as
  conditions_of gives them.  Every step takes its theorem as the derivation has it: the
  rule of a solution on the theorems of its premises, an equation backwards.  No step
  unifies*)
fun goal_thm ctxt (Goal {form, solutions, ...}) conditions =
  let
    val cterm = Thm.cterm_of ctxt;
    fun backwards eq th =
      (case eq of SOME eq' => Thm.equal_elim (Thm.symmetric (Lazy.force eq')) th | NONE => th);

    (*the alternatives nest to the right*)
    fun cases [solution] th = solution_thm solution th
      | cases (solution :: rest) th =
          let
            val (P, Q) = Thm.dest_binop (HOLogic.dest_judgment (Thm.cprop_of th));
            val (cP, cQ) = apply2 HOLogic.mk_judgment (P, Q);
            val left = solution_thm solution (Thm.assume cP);
            val R = HOLogic.dest_judgment (Thm.cprop_of left);
          in
            Drule.implies_elim_list
              \<^instantiate>\<open>P and Q and R in
                lemma (open) \<open>P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R\<close> by (rule disjE)\<close>
              [th, Thm.implies_intr cP left, Thm.implies_intr cQ (cases rest (Thm.assume cQ))]
          end
      | cases [] _ = raise Fail "Concept_Intro_Table.goal_thm: a goal without a solution"

    and solution_thm (Solution {rule, premises, ...}) th =
      let
        val rule' = Lazy.force rule;
        val parts = if null premises then [] else conjuncts (length premises) th;
      in
        Drule.implies_elim_list rule'
          (@{map 3} premise_thm premises (Thm.prems_of rule') parts)
      end

    (*the premise of the rule as the rule has it, from the theorem of what it leaves*)
    and premise_thm (Remaining (condition as {simp, ...})) _ th =
          backwards simp (prop_of_formula ctxt (shown_condition condition) th)
      | premise_thm (Concept {params, hyps, derivation}) prem th =
          let
            (*what the premise leaves, under its parameters and hypotheses again*)
            val left =
              under {params = params, hyps = hyps}
                (HOLogic.mk_Trueprop (conditions_of derivation));
            val opened =
              fold (Thm.forall_elim o cterm o Free o #2) params (prop_of_formula ctxt left th);
            (*the parameters and the hypotheses in the places that the premise has for them*)
            fun close (\<^Const_>\<open>Pure.all _ for \<open>Abs (_, _, A)\<close>\<close>) ((_, x) :: xs) hyps' =
                  Thm.forall_intr (cterm (Free x)) (close (Term.subst_bound (Free x, A)) xs hyps')
              | close (\<^Const_>\<open>Pure.imp for A B\<close>) xs hyps' =
                  Thm.implies_intr (cterm A) (close B xs (Thm.assume (cterm A) :: hyps'))
              | close _ _ hyps' =
                  goal_thm ctxt derivation (Drule.implies_elim_list opened (rev hyps'));
          in close prem params [] end;
  in backwards form (cases solutions conditions) end;

datatype failure = No_Plan | User_Limit | Not_Concept_Goal;

datatype 'a result = Found of {value: 'a, cut_short: bool} | Failed of failure;



(** an introduction rule: where it is declared, its strengthening, what a declaration refuses **)

val extraction_limit = Attrib.setup_config_int \<^binding>\<open>concept_extraction_limit\<close> (K 300);
val extraction_trace = Attrib.setup_config_bool \<^binding>\<open>concept_extraction_trace\<close> (K false);

(*The application of a declaration to one level of a local theory does nothing: the one to
  the theory has put the entry where every level reads it.  A stock locale without an
  interpretation has no application to the theory, so there a declaration registers nothing
  until an interpretation: a known limitation.  In a proof, and on an assumption of a
  statement, the entry goes to the context*)
fun on_level (Context.Proof ctxt) =
      not (Variable.is_body ctxt) andalso not (Proof_Context.is_stmt ctxt)
  | on_level (Context.Theory _) = false;

(*What goes into the table for a fact (2.5 of the plan of defining contexts).  On a structure u
  made by an instance declared as D, a fact whose concept does not give D gets a companion
  that concludes D u, from the theorem of the instance.  The companion replaces the fact where
  it gives the fact back: where the concept of the fact is above D and no truncation stays
  below it.  Else both go in, the companion as unsafe*)
fun strengthened ctxt (fact, safety) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val form = Form.conclusion fact;
    val C = Form.concept form;
    val u = Form.inner form;
    val unchanged = [(fact, safety)];
  in
    (case Term.head_of u of
      Const (c, _) =>
        (case (Concept_Type.get_instance thy c, Concept_Package.instance_facts thy c) of
          (SOME {concept = (_, D), ...}, SOME {of_concept, ...}) =>
            if C = D orelse is_some (Concept_Package.entailment thy C D) then unchanged
            else
              (case try (fn th => th RS of_concept) (Form.base_thm ctxt fact) of
                SOME th =>
                  let val companion = the (Form.of_thm ctxt th) in
                    if is_some (Concept_Package.entailment thy D C) andalso
                      Form.structure_term form aconv u
                    then [(companion, safety)]
                    else unchanged @ [(companion, Unsafe)]
                  end
              | NONE => unchanged)
        | _ => unchanged)
    | _ => unchanged)
  end;

(*the shapes that a declaration of concept_intro refuses; it gives the fact of the rule*)
fun check_rule ctxt th =
  let
    val print = quote o Syntax.string_of_term ctxt;
    val fact =
      (case Form.of_thm ctxt th of
        SOME fact => fact
      | NONE =>
          error ("A concept_intro rule cannot have a conclusion that is not a concept fact. \
            \The conclusion of your rule must have the form \"concept_predicate structure\""));
    val form = Form.conclusion fact;
    val _ =
      (case schematic_head form of
        SOME head =>
          error ("A concept_intro rule cannot have a conclusion about an arbitrary " ^
            quote (Proof_Context.extern_const ctxt (Form.concept form)) ^
            " structure. The " ^ Syntax.string_of_term ctxt head ^ " in your " ^
            print (HOLogic.dest_Trueprop (Thm.concl_of th)) ^ " must not be a variable")
      | NONE => ());
  in fact end;



(** theorems that assumption destruction is not to take **)

(*the mark of a theorem that assumption destruction has dealt with, or that it has made: the
  hook on the facts of a context lets such a theorem pass (2.1 of the plan of defining
  contexts)*)
val handledN = "concept_handled";

fun mark_handled th = Thm.tag_rule (handledN, "") th;

fun is_handled th = Properties.defined (Thm.get_tags th) handledN;



(** extraction rules **)

(*A rule that takes a proposition apart which is no concept fact, such as sub C G H ==> C G
  (section 4 of the plan of defining contexts).  The proposition is matched against its first
  premise; further premises stay on what it takes out, as in ALL x:A. P x ==> x : A ==> P x.
  The rules are kept in beta-eta normal form, by their first premises.  The store holds
  declarations: each has a key of
  its own, the theory of the declaration and its number among those of that theory, so a merge
  of theories is a union.  The rules of one proposition are used in the order of their keys,
  whatever the order of the imports.  A rule declared more than once, also with other names of
  its variables, is used once, at its least key: within one theory its first declaration,
  between theories the declaration in the theory whose full name comes first, even when that
  theory imports the other*)

type extraction = {rule: thm, key: string * int};

structure Extractions = Theory_Data
(
  type T = extraction Item_Net.T;
  val empty =
    Item_Net.init (fn (e: extraction, e': extraction) => #key e = #key e')
      (single o Logic.dest_implies o Thm.prop_of o #rule #> map #1);
  val merge = Item_Net.merge;
);

(*the rules whose premise a proposition in beta-eta normal form matches*)
fun extractions_for thy prop =
  Item_Net.retrieve_matching (Extractions.get thy) prop
  |> filter (fn {rule, ...} => Pattern.matches thy (hd (Thm.prems_of rule), prop))
  |> sort (prod_ord string_ord int_ord o apply2 #key)
  |> distinct (op aconv o apply2 (canonical o Thm.prop_of o #rule))
  |> map (Thm.transfer thy o #rule);

local

fun plural [x] = x
  | plural xs = commas (#1 (split_last xs)) ^ " and " ^ #2 (split_last xs);

(*a variable of the premise applied to something that leaves the matching several answers:
  anything but distinct bound variables.  The argument comes back with the names of the bound
  variables around it, innermost first in bs, as the user wrote it*)
fun applied_variable t =
  let
    fun bad_argument seen (arg :: args) =
          (case arg of
            Bound i => if member (op =) seen i then SOME arg else bad_argument (i :: seen) args
          | _ => SOME arg)
      | bad_argument _ [] = NONE;
    fun find bs t =
      (case strip_comb t of
        (head as Var _, args as _ :: _) =>
          (case bad_argument [] args of
            SOME arg => SOME (head, Term.subst_bounds (map Free bs, arg))
          | NONE => get_first (find bs) args)
      | (Abs (x, T, body), args) =>
          (case find ((singleton (Name.variant_list (map #1 bs)) x, T) :: bs) body of
            NONE => get_first (find bs) args
          | found => found)
      | (_, args) => get_first (find bs) args);
  in find [] t end;

in

(*the shapes that a declaration refuses, in the texts that the owner approved.  The shape is
  that of the rule in beta-eta normal form, th; the texts quote parts of the rule as the user
  wrote it*)
fun check_extraction ctxt written th =
  let
    val thy = Proof_Context.theory_of ctxt;
    val show = Syntax.string_of_term ctxt;
    val written_prem = quote (show (the_default Term.dummy (try hd (Thm.prems_of written))));
    fun refuse what = error ("A concept_extraction rule " ^ what);
    val prems = Thm.prems_of th;
    val prem =
      (case prems of
        prem :: _ => prem
      | [] => refuse "must have at least one premise");
    (*how the texts name the premise that a proposition is matched against*)
    val premise = if length prems = 1 then "premise" else "first premise";
    val concl = Thm.concl_of th;
    val body = (case prem of \<^Const_>\<open>Trueprop for A\<close> => A | _ => prem);
    val concl_body =
      (case concl of
        \<^Const_>\<open>Trueprop for A\<close> => A
      | _ =>
          refuse ("cannot have a conclusion that is not a proposition of HOL: " ^
            quote (show (Thm.concl_of written))));
    fun split kind =
      refuse ("cannot have " ^ kind ^ " as its " ^ premise ^ ". The " ^ written_prem ^
        " in your rule is split before any concept_extraction rule is tried");
    val _ =
      (case concl_body of
        \<^Const_>\<open>conj for _ _\<close> =>
          refuse "cannot have a conjunction as its conclusion. Split your rule into one rule \
            \for each conjunct"
      | _ => ());
    val _ =
      if is_some (dest_fact thy prem) then
        refuse ("cannot have a concept fact as its " ^ premise ^ ". The " ^ written_prem ^
          " in your rule is taken apart by concept instances")
      else ();
    val _ =
      (case body of
        \<^Const_>\<open>conj for _ _\<close> => split "a conjunction"
      | \<^Const_>\<open>All _ for _\<close> => split "a universal quantification"
      | \<^Const_>\<open>Pure.all _ for _\<close> => split "a universal quantification"
      | _ => ());
    val _ =
      (case Term.head_of body of
        head as Var _ =>
          refuse ("cannot have a " ^ premise ^ " that fits any proposition. The " ^ show head ^
            " in your rule must not be a variable")
      | _ => ());
    val _ =
      (case applied_variable body of
        SOME (head, arg) =>
          refuse ("cannot have a " ^ premise ^ " that applies a variable to a term. The " ^
            show head ^ " in your rule must not be applied to " ^
            (if is_Var arg then show arg else quote (show arg)))
      | NONE => ());
    (*the further premises stay on what the rule takes out: a variable of the conclusion may
      come from any of them*)
    val _ =
      (case subtract (op =) (fold Term.add_vars prems []) (rev (Term.add_vars concl [])) of
        [] => ()
      | vars =>
          refuse ("cannot have a conclusion containing " ^
            (if length vars = 1 then "a variable" else "variables") ^ " unconstrained in the " ^
            (if length prems = 1 then "premise" else "premises") ^ ": " ^
            plural (map (show o Var) vars)));
    (*the variable at the head of the conclusion must come from the first premise, the only
      one that is matched*)
    val _ =
      (case Term.head_of concl_body of
        head as Var v =>
          if member (op =) (Term.add_vars prem []) v then ()
          else
            refuse ("cannot have a conclusion starting with a variable unconstrained in the \
              \first premise: " ^ show head)
      | _ => ());
  in () end;

end;

(*the rules live in the theory: a declaration in a proof, or on an assumption of a statement,
  is refused; its application to a level of a local theory does nothing*)
fun register_extraction th context =
  (case context of
    Context.Theory thy =>
      let
        val ctxt = Proof_Context.init_global thy;
        val rule = Conv.fconv_rule Drule.beta_eta_conversion th;
        val _ = check_extraction ctxt th rule;
        val name = Context.theory_long_name thy;
        val number =
          length (filter (fn {key, ...} => #1 key = name) (Item_Net.content (Extractions.get thy)));
      in
        Context.Theory
          (Extractions.map
            (Item_Net.update {rule = Thm.trim_context rule, key = (name, number)}) thy)
      end
  | Context.Proof _ =>
      if on_level context then context
      else error "Cannot declare a concept_extraction rule inside a proof context");

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>concept_extraction\<close>
      (Scan.succeed (Thm.declaration_attribute register_extraction))
      "declaring a so-called extraction rule, used to extract concept facts from the applicable \
      \propositions");




(** assumption destruction **)

(*What happens to a fact that enters a context (sections 2 and 4A of the plan of defining
  contexts).  The fact is taken apart: conjunctions and universal quantifications are opened,
  the instance term of a concept fact gives what the instance was declared with, a relation
  fact gives what the extraction rules make of it.  A fact may have premises: every step reads
  its conclusion, and the premises stay on what the step gives; they are never taken apart
  themselves.  Each concept fact on the way goes into the table, strengthened, and is
  activated: the activation list of its concept gives more entries.  The work is done in rounds,
  each a first stage in breadth-first order and then its activations; what an activation result
  needs beyond its list, its further work, belongs to the next round.  A check on the chain of
  steps of each node lets the work end.  A limit on the counted steps of one fact keeps it
  short; what the limit stops is recorded, and done when a later fact comes to it*)

(*what a call does beside that, and where it is made (the table of 4A.3): the site sets the
  limit and what is recorded*)
type destruct_work = {safe_intro: bool, notation: bool, masked_entries: bool};

datatype site = In_Context | Internal_Call | Host_Premise | Theory_Level;


(* activation lists *)

(*by concept C: theorems C ?S ==> ..., each a fact that holds where C holds*)
structure Activation = Theory_Data
(
  type T = thm list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

fun activation_list thy C = map (Thm.transfer thy) (Symtab.lookup_list (Activation.get thy) C);


(* what a context keeps beside its entries *)

(*What an activation result needs beyond the list that gave it (4A.3).  changed: the selector
  Simpset has changed the head of its structure; apart: into an instance, whose term is to be
  taken apart; supplements: the new entries that strengthening gave it in another concept, each
  with a list still to activate*)
type further = {fact: Form.fact, changed: bool, apart: bool, supplements: Form.fact list};

(*A piece of work that the limit has stopped (4A.5): a node that passed the check, with the
  step that the limit refused it.  record: that of the node as it arrived, without the node.
  recorder: the key of the fact that came in for the traversal which recorded the piece.
  names: the entries under which the piece is named; a node that meets one of them continues
  the piece.  Only a call without a mask leaves pieces*)
datatype stopped_step =
  Apply_Rules of thm         (*to a relation fact*)
| Take_Apart of Form.fact    (*a concept fact of the first stage*)
| Further_Work of further;   (*of an activation result in the table*)

type stopped =
 {step: stopped_step, record: Concept_Check.record, recorder: term, names: Termset.T};

(*the kind of a step and the key of its proposition*)
fun step_key (Apply_Rules th) = (0, canonical (Thm.prop_of th))
  | step_key (Take_Apart fact) = (1, entry_prop fact)
  | step_key (Further_Work {fact, ...}) = (2, entry_prop fact);

(*one piece: the same step on the same proposition, the same record, the same recorder*)
fun same_stopped (piece: stopped, piece': stopped) =
  eq_pair (op =) (op aconv) (step_key (#step piece), step_key (#step piece')) andalso
  #recorder piece aconv #recorder piece' andalso
  Concept_Check.same (#record piece, #record piece');

fun add_names names ({step, record, recorder, names = names'}: stopped) : stopped =
  {step = step, record = record, recorder = recorder, names = Termset.merge (names', names)};

(*The propositions that have gone through the first stage in a context (4A.4), by their keys:
  that of a concept fact, any other proposition in beta-eta normal form with canonical
  variables.  A fact that came in and below which the limit has left work is capped at that
  limit, and keeps what its context had before it was taken apart.  A key has one note usable
  everywhere, written by a call without a mask, or one note for each premise of the simplifier
  that took the proposition apart*)
datatype status =
  Not_Capped
| Capped of
   {limit: int, entries: table, seen: status masked Termtab.table, stopped: stopped list};

(*stopped: in the order in which the pieces were recorded*)
structure Destruction = Proof_Data
(
  type T = {seen: status masked Termtab.table, stopped: stopped list};
  fun init _ = {seen = Termtab.empty, stopped = []};
);

fun map_seen f = Destruction.map (fn {seen, stopped} => {seen = f seen, stopped = stopped});
fun map_stopped f = Destruction.map (fn {seen, stopped} => {seen = seen, stopped = f stopped});

(*what the set says of a key to a call with this mask*)
fun noted ctxt mask seen key = Option.mapPartial (serving ctxt mask) (Termtab.lookup seen key);

fun add_note mask (key, status) seen =
  Termtab.update (key, add_masked (mask, status) (Termtab.lookup seen key)) seen;

(*for tests: the keys of the facts that are capped, each with its limit; the stopped work,
  each piece by the key of its proposition with the entries under which it is named*)
fun destruction_state ctxt =
  let val {seen, stopped} = Destruction.get ctxt in
    {capped =
       Termtab.fold (fn (key, note) =>
         (case usable ctxt note of SOME (Capped {limit, ...}) => cons (key, limit) | _ => I)) seen [],
     stopped = map (fn {step, names, ...} => (#2 (step_key step), Termset.dest names)) stopped}
  end;

(*the entries of a concept fact: what its step into the table puts or meets*)
fun entries_of ctxt fact = map (entry_prop o #1) (strengthened ctxt (fact, Unsafe));

(*the mark of what a traversal or the handler of simp puts: a fact without premises is safe;
  under premises it is a rule whose premises are only sufficient*)
fun put_safety fact = if Thm.no_prems (Form.thm_of fact) then Safe_By_System else Unsafe;

(*a fact goes into the table of a context, with a mask or none: it is strengthened, and each
  entry is put unless the table has what serves; each registration with whether it is new*)
fun put_strengthened mask fact ctxt =
  fold_map (fn (fact', safety) => fn ctxt' =>
      let
        val registration: registration =
          {fact = fact', user = false, safety = safety, mask = mask, pos = Position.none};
        val (new, ctxt'') = add_contextual registration ctxt';
      in ((registration, new), ctxt'') end)
    (strengthened ctxt (fact, put_safety fact)) ctxt;

(*what the set says of a concept fact to a call with this mask (4A.4).  A fact recorded as not
  capped counts as absent while work is named under an entry of it: it goes through the first
  stage once more, and so comes to that work*)
fun status_of ctxt mask fact =
  (case noted ctxt mask (#seen (Destruction.get ctxt)) (entry_prop fact) of
    SOME Not_Capped =>
      (case #stopped (Destruction.get ctxt) of
        [] => SOME Not_Capped
      | work =>
          if exists (fn entry => exists (fn piece => Termset.member (#names piece) entry) work)
            (entries_of ctxt fact)
          then NONE else SOME Not_Capped)
  | status => status);


(* the parts of a fact *)

(*a theorem in the form of a fact that comes in: HHF, its outer parameters schematic, in
  beta-eta normal form*)
fun normal ctxt th =
  Raw_Simplifier.norm_hhf ctxt th |> Conv.fconv_rule Drule.beta_eta_conversion;

(*a rule with its first premise matched against the conclusion of a theorem, the theorem put in
  its place: the premises of the theorem first, then the other premises of the rule.  The match
  binds only the variables of the rule, whose indexes lie above those of the theorem; the
  composition has nothing left to unify, so the variables of the theorem stay*)
fun elim_first ctxt rule th =
  let
    val rule' = Thm.incr_indexes (Thm.maxidx_of th + 1) rule;
    val env =
      Pattern.match (Proof_Context.theory_of ctxt)
        (Envir.beta_eta_contract (Thm.major_prem_of rule'), Thm.concl_of th)
        (Vartab.empty, Vartab.empty);
  in
    Thm.bicompose (SOME ctxt) {flatten = false, match = true, incremented = true}
      (false, th, Thm.nprems_of th) 1 (instance_of ctxt env rule')
    |> Seq.hd |> normal ctxt
  end;

(*a theorem opened at the conjunctions and universal quantifications of HOL at the head of its
  conclusion, each part in beta-eta normal form; its premises stay on every part*)
fun open_fact th =
  (case Thm.concl_of th of
    \<^Const_>\<open>Trueprop for \<^Const_>\<open>conj for _ _\<close>\<close> =>
      open_fact (th RS @{thm conjunct1}) @ open_fact (th RS @{thm conjunct2})
  | \<^Const_>\<open>Trueprop for \<^Const_>\<open>All _ for _\<close>\<close> => open_fact (th RS @{thm spec})
  | _ => [Conv.fconv_rule Drule.beta_eta_conversion th]);

(*what a part is to the traversal, read off its conclusion; its premises are carried along
  and never taken apart.  Concept_Fact: the conclusion is C t.  Relation: the conclusion is a
  proposition R ts of HOL that is no concept fact, for a constant R, given without Trueprop*)
datatype leaf = Concept_Fact of Form.fact | Relation of term | Nothing;

fun leaf_of ctxt th =
  (case Form.of_thm ctxt th of
    SOME fact =>
      if is_some (schematic_head (Form.conclusion fact)) then Nothing else Concept_Fact fact
  | NONE =>
      (case Thm.concl_of th of
        \<^Const_>\<open>Trueprop for A\<close> => if is_Const (Term.head_of A) then Relation A else Nothing
      | _ => Nothing));

(*the key of a part in the set and among the propositions taken apart*)
fun leaf_key th (Concept_Fact fact) = entry_prop fact
  | leaf_key th _ = canonical (Thm.prop_of th);

(*the conditions of the instance that makes a structure, as theorems of concept u, where u is
  made by an instance that has such theorems*)
fun instance_destructions thy u =
  (case Term.head_of u of
    Const (c, _) =>
      (case Concept_Package.instance_facts thy c of
        SOME {destructions, ...} => map #2 destructions
      | NONE => [])
  | _ => []);

(*a structure below the constants of views at its head*)
fun below_views thy t =
  (case Concept_Type.dest_view thy t of SOME s => below_views thy s | NONE => t);

(*the heads of two structures are the same: a constant is its name (4A.1)*)
fun same_head (Const (c, _), Const (c', _)) = c = c'
  | same_head (t, t') = t aconv t';


(* the messages of the trace *)

(*the step that the check has kept from a node*)
datatype kept = No_Rules | No_Instance | No_Supplement of string;

fun trace ctxt lines =
  if Config.get ctxt extraction_trace then warning (cat_lines (lines ())) else ();

(*a node failed the check; elsewhere: another chain of steps took its proposition apart*)
fun failure_lines ctxt {internal} prop reason kept elsewhere =
  let
    val show = Syntax.string_of_term ctxt;
    val start = "concept extraction did not take a proposition further: ";
    val so =
      "  so: " ^
      (case kept of
        No_Rules => "no extraction rule was applied to it."
      | No_Instance => "its instance was not taken apart."
      | No_Supplement D =>
          "it did not get the supplementary activation of " ^
          Proof_Context.extern_const ctxt D ^ ".");
    val proposition = "  proposition: " ^ show prop;
  in
    (case reason of
      Concept_Check.Grows_Again {from, same, grew} =>
        if from aconv grew then
          [start ^ "it grows from an earlier fact of its chain of steps that grew itself.",
           proposition, "  grows from: " ^ show from]
        else if same then
          [start ^ "it is an earlier fact of its chain of steps again, apart from types and \
            \the names of schematic and bound variables, and another fact of that chain grew \
            \already.",
           proposition, "  again: " ^ show from, "  grew already: " ^ show grew]
        else
          [start ^ "it grows from an earlier fact of its chain of steps, and another fact of \
            \that chain grew already.",
           proposition, "  grows from: " ^ show from, "  grew already: " ^ show grew]
    | Concept_Check.Contains sources =>
        [start ^ "it contains " ^ (if internal then "two" else "three") ^
          " earlier facts of its chain of steps whose arguments differ.", proposition] @
        map (fn p => "  contains: " ^ show p) (take (if internal then 2 else 3) sources)) @
    [so] @ (if elsewhere then ["  another chain of steps took it apart."] else [])
  end;

fun pieces_of_work 1 = "1 piece of work" | pieces_of_work n = string_of_int n ^ " pieces of work";


(* a traversal *)

(*the nodes whose proposition was taken apart, by class (4A.1): a fact of the first stage; an
  activation result whose head the simplification has changed; one whose head it has left*)
datatype class = First | Changed | Unchanged;

fun class_of ({changed, ...}: further) = if changed then Changed else Unchanged;

type node =
 {id: int,
  parent: int option,    (*the node of the step that gave it: a rule or an instance*)
  thm: thm, leaf: leaf, key: term,
  record: Concept_Check.record,
  chain: term list,      (*the entries of the concept facts on its chain, across activations*)
  inherited: Termset.T,  (*the names of the piece to whose continuation it belongs*)
  table: int,            (*its table of propositions taken apart*)
  second: bool,          (*in the second pass*)
  derived: bool,         (*by a rule or from an instance*)
  stated: bool,          (*the fact that came in, or a part of it*)
  root: bool};           (*the fact that came in*)

fun in_second_pass
    ({id, parent, thm, leaf, key, record, chain, inherited, table, derived, stated, root,
      ...}: node) : node =
  {id = id, parent = parent, thm = thm, leaf = leaf, key = key, record = record, chain = chain,
   inherited = inherited, table = table, second = true, derived = derived, stated = stated,
   root = root};

(*what waits for the end of a round*)
datatype scheduled =
  (*an activation result that needs more than its list; first: it had not appeared in its
    table before, so its further work counts (4A.3)*)
  Result of {node: node, work: further, first: bool}
  (*a node has met an entry: the pieces named under the entry are to be continued*)
| Continue of {pieces: stopped list, at: node, entry: term};

(*The fact root, in beta-eta normal form and without outer quantifiers, is taken apart in ctxt0.
  limit: of its count, none where the site has none.  two_groups: what the first pass does with
  a relation fact that contains two earlier facts of its chain; with Refused there is no second
  pass.  recorder: the key of the fact.  own_variables: the variables of a rule that is
  registered in a theory, fixed for this traversal; a fact on such a variable is put and not
  activated: where the rule is used the variable is schematic, and a proof that has the same
  theorem makes nothing of such a fact.  It gives the new context, the entries put, and whether
  the limit has left work below the fact (4A.4)*)
fun traverse {limit, two_groups, safe_intro, mask, recorder, own_variables} root ctxt0 =
  let
    val thy = Proof_Context.theory_of ctxt0;
    fun on_own_variable fact =
      (case Term.head_of (Form.inner (Form.conclusion fact)) of
        Free (x, _) => member (op =) own_variables x
      | _ => false);
    val reading: Concept_Check.reading =
     {fixed = Variable.is_fixed ctxt0,
      concept_name =
        (fn Const (c, _) => is_some (Concept.concept_of_predicate thy c) | _ => false),
      below_views = below_views thy,
      structure_type = is_some o Concept_Type.dest_scheme_type thy};
    val internal = two_groups = Concept_Check.Refused;


    (* what the traversal changes *)

    val context = Unsynchronized.ref ctxt0;
    val count = Unsynchronized.ref 0;
    fun full () = (case limit of SOME n => ! count >= n | NONE => false);
    val ids = Unsynchronized.ref 0;    (*of nodes and of tables*)

    (*by table: the propositions taken apart with the node that took each, and the concept
      facts that have appeared, of which only a first appearance counts (4A.3)*)
    val taken =
      Unsynchronized.ref (Inttab.empty: (class * int) list Termtab.table Inttab.table);
    val appeared = Unsynchronized.ref (Inttab.empty: Termset.T Inttab.table);

    (*for the end: the nodes, what each node that went on has added to the record of its
      chain, the entries of each concept fact, the entries put, what the limit refused, what
      failed the check, the nodes incomplete by a failure, the nodes passed over for another
      one that took their proposition, the entries met with the chains that met them*)
    val nodes = Unsynchronized.ref ([]: node list);
    val parents = Unsynchronized.ref (Inttab.empty: int option Inttab.table);
    val advances =
      Unsynchronized.ref
        (Inttab.empty: (Concept_Check.record -> Concept_Check.record) Inttab.table);
    val entries = Unsynchronized.ref (Inttab.empty: term list Inttab.table);
    val put = Unsynchronized.ref ([]: registration list);
    val refusals = Unsynchronized.ref ([]: (node * stopped_step) list);
    val failures = Unsynchronized.ref ([]: (node * Concept_Check.reason * kept * class) list);
    val restricted = Unsynchronized.ref (Inttab.empty: Inttab.set);
    val skips = Unsynchronized.ref ([]: (int * int) list);
    val meetings = Unsynchronized.ref ([]: (term * term list) list);

    (*within a round: the new entries of the first stage to activate, what waits for the end
      of the round, the supplementary activations of the coming round; over the rounds: the
      relation facts set aside, the pieces that a meeting has scheduled*)
    val entered =
      Unsynchronized.ref
        ([]: {fact: Form.fact, node: node, record: Concept_Check.record, chain: term list} list);
    val scheduled = Unsynchronized.ref ([]: scheduled list);
    val supplementary = Unsynchronized.ref ([]: (unit -> unit) list);
    val aside = Unsynchronized.ref ([]: node list);
    val met = Unsynchronized.ref ([]: stopped list);

    fun taken_by ({table, key, ...}: node) class =
      AList.lookup (op =)
        (Termtab.lookup_list (the_default Termtab.empty (Inttab.lookup (! taken) table)) key) class;
    fun set_taken ({table, key, id, ...}: node) class =
      Unsynchronized.change taken
        (Inttab.map_default (table, Termtab.empty) (Termtab.cons_list (key, (class, id))));
    fun has_appeared ({table, key, ...}: node) =
      (case Inttab.lookup (! appeared) table of
        SOME facts => Termset.member facts key
      | NONE => false);
    fun appear ({table, key, ...}: node) =
      Unsynchronized.change appeared
        (Inttab.map_default (table, Termset.empty) (Termset.insert key));
    fun entries_at ({id, ...}: node) = these (Inttab.lookup (! entries) id);


    (* nodes *)

    fun make {parent, record, chain, inherited, table, second, derived, stated, root}
        (th, leaf) =
      let
        val nd: node =
         {id = Unsynchronized.inc ids, parent = parent, thm = th, leaf = leaf,
          key = leaf_key th leaf, record = record, chain = chain, inherited = inherited,
          table = table, second = second, derived = derived, stated = stated, root = root};
      in
        Unsynchronized.change nodes (cons nd);
        Unsynchronized.change parents (Inttab.update (#id nd, parent));
        nd
      end;

    (*what a rule or an instance gives of a node*)
    fun child (nd: node) record chain part =
      make
       {parent = SOME (#id nd), record = record, chain = chain, inherited = #inherited nd,
        table = #table nd, second = #second nd, derived = true, stated = false, root = false}
        part;

    (*a concept fact that a rule or an instance gives counts where it appears first in its
      table, unless the set lets it pass (4A.3)*)
    fun count_derived (nd: node) =
      (case #leaf nd of
        Concept_Fact fact =>
          if has_appeared nd orelse is_some (status_of (! context) mask fact) then ()
          else (appear nd; ignore (Unsynchronized.inc count))
      | _ => ());

    fun advance ({id, ...}: node) add = Unsynchronized.change advances (Inttab.update (id, add));

    (*A node failed the check.  The node, and each node above it for which the check passes
      with the facts from that node on alone, is incomplete by it (the second cause of 4A.4)*)
    fun fail (nd: node) reason kept class passes =
      let
        fun mark id path =
          if passes (fold (fn add => fn record => add record) path Concept_Check.empty) then
            (Unsynchronized.change restricted (Inttab.insert_set id);
             (case the (Inttab.lookup (! parents) id) of
               SOME above => mark above (the_default I (Inttab.lookup (! advances) above) :: path)
             | NONE => ()))
          else ();
      in
        Unsynchronized.change failures (cons (nd, reason, kept, class));
        mark (#id nd) []
      end;

    fun skip ({id, ...}: node) first = Unsynchronized.change skips (cons (id, first));
    fun refuse nd step = Unsynchronized.change refusals (cons (nd, step));


    (* the table *)

    (*a node meets an entry (4A.5): the pieces named under the entry are to be continued, a
      piece once in a traversal*)
    fun meet (nd: node) entry =
      let
        val pieces =
          #stopped (Destruction.get (! context)) |> filter (fn piece =>
            Termset.member (#names piece) entry andalso not (member same_stopped (! met) piece));
      in
        Unsynchronized.change meetings (cons (entry, entry :: #chain nd));
        if null pieces then ()
        else
          (Unsynchronized.change met (append pieces);
           Unsynchronized.change scheduled
             (cons (Continue {pieces = pieces, at = nd, entry = entry})))
      end;

    (*the step of a fact into the table; each entry with whether it is new*)
    fun put_entries fact =
      let val (results, ctxt) = put_strengthened mask fact (! context) in
        context := ctxt;
        results |> List.app (fn (registration, new) =>
          if new then Unsynchronized.change put (cons registration) else ());
        map (fn (registration: registration, new) => (#fact registration, new)) results
      end;

    fun set_entries ({id, ...}: node) facts =
      Unsynchronized.change entries (Inttab.update (id, map entry_prop facts));


    (* the first stage *)

    (*the conditions of an instance on a concept fact: the parts of the node*)
    fun parts (nd: node) fact record chain =
      let
        val ctxt = ! context;
        val base = Form.base_thm ctxt fact;
        val children =
          instance_destructions thy (Form.inner (Form.conclusion fact))
          |> maps (fn condition => open_fact (elim_first ctxt condition base))
          |> map (fn th => child nd record chain (th, leaf_of ctxt th));
      in List.app count_derived children; children end;

    fun check_fact fact record =
      let val form = Form.conclusion fact in
        Concept_Check.concept_fact reading record (Form.concept form) (Form.inner form)
          (HOLogic.dest_Trueprop (Form.prop form))
      end;

    (*whether a check lets a fact go on under a record, and the record with the fact*)
    fun passes check record =
      (case check record of Concept_Check.Fails _ => false | _ => true);
    fun adding check record =
      (case check record of Concept_Check.Passes record' => record' | _ => record);

    (*a node goes on: its proposition is taken in its table, and add, what it adds to the
      record of its chain, is kept; it gives the record below the node*)
    fun go_on (nd: node) class add = (set_taken nd class; advance nd add; add (#record nd));

    (*the instance term of a fact of the first stage is taken apart*)
    fun take_apart (nd: node) fact =
      parts nd fact (go_on nd First (adding (check_fact fact))) (entries_at nd @ #chain nd);

    fun visit_fact (nd: node) fact =
      (case if #root nd then NONE else status_of (! context) mask fact of
        SOME (Capped _) =>
          (*passed over, but it meets its entries*)
          let val own = entries_of (! context) fact in
            Unsynchronized.change entries (Inttab.update (#id nd, own));
            List.app (meet nd) own;
            []
          end
      | SOME Not_Capped => []
      | NONE =>
          let
            val instance =
              not (null (instance_destructions thy (Form.inner (Form.conclusion fact))));
            val first = if instance then taken_by nd First else NONE;
            val verdict =
              if instance andalso is_none first then SOME (check_fact fact (#record nd)) else NONE;
            (*what its activation results carry: the fact is in it where it passed the check*)
            val record = (case verdict of SOME (Concept_Check.Passes r) => r | _ => #record nd);
            val results = put_entries fact;
            val _ = set_entries nd (map #1 results);
            val chain = entries_at nd @ #chain nd;
            val _ = results |> List.app (fn (fact', new) =>
              if not new then meet nd (entry_prop fact')
              else if on_own_variable fact' then ()
              else
                Unsynchronized.change entered
                  (cons {fact = fact', node = nd, record = record, chain = chain}));
            val _ =
              if safe_intro then
                context :=
                  Classical.addSIs (! context,
                    filter Thm.no_prems
                      (distinct Thm.eq_thm_prop
                        (Form.thm_of fact :: map (Form.thm_of o #1) (filter #2 results))))
              else ();
          in
            (case (first, verdict) of
              (SOME first', _) => (skip nd first'; [])
            | (NONE, SOME (Concept_Check.Fails reason)) =>
                (fail nd reason No_Instance First (passes (check_fact fact)); [])
            | (NONE, SOME (Concept_Check.Passes _)) =>
                if full () then (refuse nd (Take_Apart fact); [])
                else take_apart nd fact
            | _ => [])
          end);

    (*the extraction rules on a relation fact, all of them in one step*)
    fun apply_rules (nd: node) A rules =
      let
        val ctxt = ! context;
        fun check record = Concept_Check.relation_fact reading Concept_Check.Allowed record A;
        val record' = go_on nd First (Concept_Check.after_rule o adding check);
        val children =
          rules |> maps (fn rule =>
            open_fact (elim_first ctxt rule (#thm nd)) |> map (fn th => (th, leaf_of ctxt th)))
          |> map (child nd record' (#chain nd));
      in List.app count_derived children; children end;

    fun visit_relation (nd: node) A =
      (case extractions_for thy (Thm.concl_of (#thm nd)) of
        [] => []
      | rules =>
          (case taken_by nd First of
            SOME first => (skip nd first; [])
          | NONE =>
              let
                fun check record =
                  Concept_Check.relation_fact reading
                    (if #second nd then Concept_Check.Allowed else two_groups) record A;
              in
                (case check (#record nd) of
                  Concept_Check.Fails reason =>
                    (fail nd reason No_Rules First (passes check); [])
                | Concept_Check.Set_Aside => (Unsynchronized.change aside (cons nd); [])
                | Concept_Check.Passes _ =>
                    if full () then (refuse nd (Apply_Rules (#thm nd)); [])
                    else
                      (if #derived nd then ignore (Unsynchronized.inc count) else ();
                       apply_rules nd A rules))
              end));

    fun visit (nd: node) =
      (case #leaf nd of
        Concept_Fact fact => visit_fact nd fact
      | Relation A => visit_relation nd A
      | Nothing => []);

    fun stage queue =
      if Queue.is_empty queue then ()
      else
        let val (nd, queue') = Queue.dequeue queue
        in stage (fold Queue.enqueue (visit nd) queue') end;


    (* activation *)

    (*A list on a fact that is in the table (2.2).  A result carries the record and the chain
      given; it appears in its table (4A.3); it is put, strengthened, unless the table has it.
      A new result that needs more than the list waits for the end of the round*)
    fun activate list {fact, node = nd, record, chain} =
      list |> List.app (fn rule =>
        let
          val ctxt = ! context;
          val th = elim_first ctxt rule (Form.thm_of fact);
        in
          (case leaf_of ctxt th of
            Concept_Fact result =>
              let
                val rn =
                  make
                   {parent = NONE, record = record, chain = chain, inherited = #inherited nd,
                    table = #table nd, second = #second nd, derived = false, stated = false,
                    root = false} (th, Concept_Fact result);
                val first = not (has_appeared rn);
                val _ = appear rn;
                val results = put_entries result;
                val _ = set_entries rn (map #1 results);
                val _ = results |> List.app (fn (fact', new) =>
                  if new then () else meet rn (entry_prop fact'));
                val new = map #1 (filter #2 results);
                val form = Form.conclusion result;
                (*the head of the structure as the list gives it, and after the selector
                  Simpset*)
                val (_, _, t) = the (dest_fact thy (Thm.concl_of th));
                val changed =
                  not (same_head (Term.head_of (below thy t), Term.head_of (Form.inner form)));
                val work: further =
                 {fact = result, changed = changed,
                  apart =
                    changed andalso not (null (instance_destructions thy (Form.inner form))),
                  supplements =
                    filter (fn fact' =>
                      Form.concept (Form.conclusion fact') <> Form.concept form) new};
              in
                if not (null new) andalso (#apart work orelse not (null (#supplements work)))
                then
                  Unsynchronized.change scheduled
                    (cons (Result {node = rn, work = work, first = first}))
                else ()
              end
          | _ => ())
        end);

    (*The supplementary activation of an entry that strengthening gave a result in another
      concept: the list of that concept on the entry, without the rules that give there what
      the list of the result's own concept gives on the result; the two are on one structure*)
    fun supplement result (nd: node) record chain fact' =
      let
        val ctxt = ! context;
        fun given fact0 rule =
          canonical (Thm.prop_of (elim_first ctxt rule (Form.thm_of fact0)));
        val own =
          map (given result) (activation_list thy (Form.concept (Form.conclusion result)));
        val list =
          activation_list thy (Form.concept (Form.conclusion fact'))
          |> filter_out (member (op aconv) own o given fact');
      in activate list {fact = fact', node = nd, record = record, chain = chain} end;

    (*The further work of an activation result is done.  It gives the nodes of its instance
      term, for the first stage of the coming round, and its supplementary activations, still
      to be made*)
    fun further_work (nd: node) (work as {fact, apart, supplements, ...}: further) =
      let
        val record = go_on nd (class_of work) (adding (check_fact fact));
        val chain = entries_at nd @ #chain nd;
      in
        (if apart then parts nd fact record chain else [],
         map (fn fact' => fn () => supplement fact nd record chain fact') supplements)
      end;

    (*The further work of an activation result begins (4A.3): it is checked; where the count
      is full it becomes stopped work; else it counts, where the result appeared first with
      it, and is done*)
    fun begin_result
        {node = rn: node, work = work as {fact, apart, supplements, ...}: further, first} =
      let val class = class_of work in
        (case taken_by rn class of
          SOME taker => (skip rn taker; ([], []))
        | NONE =>
            (case check_fact fact (#record rn) of
              Concept_Check.Passes _ =>
                if full () then (refuse rn (Further_Work work); ([], []))
                else
                  (if first then ignore (Unsynchronized.inc count) else ();
                   further_work rn work)
            | Concept_Check.Fails reason =>
                (fail rn reason
                  (if apart then No_Instance
                   else No_Supplement (Form.concept (Form.conclusion (hd supplements))))
                  class (passes (check_fact fact));
                 ([], []))
            | Concept_Check.Set_Aside => ([], [])))
      end;

    (*The pieces named under an entry that a node has met are continued (4A.5): each counts 1
      and redoes its refused step under its own record, with itself added, in a table of its
      own; a piece that the count leaves no room for stays.  A step of rules or of an instance
      gives nodes for the first stage of the coming round; a supplementary activation is made
      at once*)
    fun continue {pieces, at = nd: node, entry} =
      let
        fun redo ({step, record, names, ...}: stopped) =
          let
            val ctxt = ! context;
            val table = Unsynchronized.inc ids;
            fun node part =
              make
               {parent = NONE, record = record, chain = entry :: #chain nd, inherited = names,
                table = table, second = #second nd, derived = false, stated = false,
                root = false} part;
            (*the node of a concept fact, which has appeared in its table*)
            fun fact_node fact =
              let val c = node (Form.thm_of fact, Concept_Fact fact) in
                Unsynchronized.change entries (Inttab.update (#id c, entries_of ctxt fact));
                appear c;
                c
              end;
          in
            (case step of
              Apply_Rules th =>
                let val A = HOLogic.dest_Trueprop (Thm.concl_of th) in
                  apply_rules (node (th, Relation A)) A (extractions_for thy (Thm.concl_of th))
                end
            | Take_Apart fact => take_apart (fact_node fact) fact
            | Further_Work work =>
                let val (children, supplements) = further_work (fact_node (#fact work)) work
                in List.app (fn run => run ()) supplements; children end)
          end;
        (*whether the piece is begun, with the nodes that it gives*)
        fun one piece =
          if full () then (false, [])
          else
            (context := map_stopped (remove same_stopped piece) (! context);
             ignore (Unsynchronized.inc count);
             (true, redo piece));
        val outcomes = map one pieces;
        val begun = length (filter #1 outcomes);
        val left = length outcomes - begun;
        val show = Syntax.string_of_term (! context);
        val _ =
          if begun = 0 then ()
          else
            trace (! context) (fn () =>
              ["concept extraction continued " ^ pieces_of_work begun ^
                " that the limit had stopped.",
               "  entry: " ^ show entry, "  counted for: " ^ show (Thm.prop_of root)]);
        val _ =
          if left = 0 then ()
          else
            trace (! context) (fn () =>
              ["concept extraction did not continue " ^ pieces_of_work left ^
                " that the limit had stopped: the count of the fact that reached " ^
                (if left = 1 then "it" else "them") ^ " is full.",
               "  entry: " ^ show entry, "  fact: " ^ show (Thm.prop_of root)]);
      in maps #2 outcomes end;


    (* rounds *)

    (*the activations of a round: the new entries of its first stage, each with the list of
      its concept; then the supplementary activations that belong to the round*)
    fun activation () =
      let
        val activating = rev (! entered);
        val _ = entered := [];
        val _ = activating |> List.app (fn a as {fact, ...} =>
          activate (activation_list thy (Form.concept (Form.conclusion fact))) a);
        val supplements = ! supplementary;
        val _ = supplementary := [];
      in List.app (fn run => run ()) supplements end;

    (*Between two rounds what was scheduled begins, in its order, until nothing is scheduled.
      A result whose instance term is to be taken apart begins here, and its supplementary
      activations follow in the coming round; another result begins there, with them.  It
      gives the nodes for the first stage of the coming round*)
    fun start () =
      let
        fun later runs = Unsynchronized.change supplementary (fn waiting => waiting @ runs);
        fun item (Result (result as {work, ...})) =
              if #apart work then
                let val (children, supplements) = begin_result result
                in later supplements; children end
              else (later [fn () => List.app (fn run => run ()) (#2 (begin_result result))]; [])
          | item (Continue meeting) = continue meeting;
        fun work children =
          (case rev (! scheduled) of
            [] => children
          | items => (scheduled := []; work (children @ maps item items)));
      in work [] end;

    fun rounds queue =
      (stage queue;
       activation ();
       (case start () of
         [] => if null (! supplementary) then () else rounds Queue.empty
       | children => rounds (fold Queue.enqueue children Queue.empty)));

    (*the second pass, where there is one: the relation facts set aside, in their order*)
    fun second_pass () =
      (case rev (! aside) of
        [] => ()
      | waiting =>
          (aside := [];
           rounds (fold (Queue.enqueue o in_second_pass) waiting Queue.empty);
           second_pass ()));

    (*the fact that came in; where it is a conjunction or a quantification, its parts*)
    fun stated parent is_root part =
      make
       {parent = parent, record = Concept_Check.empty, chain = [], inherited = Termset.empty,
        table = 0, second = false, derived = false, stated = true, root = is_root}
        part;
    val opened = open_fact root;
    val single = (case opened of [th] => Thm.eq_thm_prop (th, root) | _ => false);
    val root_node = stated NONE true (root, if single then leaf_of ctxt0 root else Nothing);
    val initial =
      if single then [root_node]
      else map (fn th => stated (SOME (#id root_node)) false (th, leaf_of ctxt0 th)) opened;
    (*what is stated has appeared in the table of the traversal from the start (4A.3)*)
    val _ = List.app appear initial;
    val _ = rounds (fold Queue.enqueue initial Queue.empty);
    val _ = second_pass ();


    (* the end of the traversal (4A.4, 4A.5) *)

    val ctxt1 = ! context;
    val all_nodes = rev (! nodes);
    val refused = rev (! refusals);

    (*What the limit refused becomes stopped work, named under the entries of the concept
      facts on its chain, its own among them, and under the names that it has inherited.  A
      node that met an entry and left a piece named under it: the piece is named under the
      entries of the chain of that node too; and so on until nothing changes*)
    fun record_piece (piece: stopped) pieces =
      if member same_stopped pieces piece then
        pieces |> map (fn piece' =>
          if same_stopped (piece', piece) then add_names (#names piece) piece' else piece')
      else pieces @ [piece];
    fun close pieces =
      let
        val pieces' = pieces |> map (fn piece =>
          fold (fn (entry, chain) => fn piece': stopped =>
            if Termset.member (#names piece') entry then add_names (Termset.make chain) piece'
            else piece') (! meetings) piece);
      in
        if eq_list (fn (piece: stopped, piece': stopped) =>
            Termset.subset (#names piece', #names piece)) (pieces, pieces')
        then pieces
        else close pieces'
      end;
    val stopped =
      refused |> map (fn (nd, step) =>
        {step = step, record = #record nd, recorder = recorder,
         names = Termset.merge (Termset.make (entries_at nd @ #chain nd), #inherited nd)}: stopped)
      |> (fn pieces => fold record_piece pieces (#stopped (Destruction.get ctxt1)))
      |> close;
    val named = Termset.merges (map #names stopped);

    (*The nodes that are not complete (4A.4).  First cause: a node with something below it,
      itself included, that the limit refused, or with a concept fact below it under whose
      entry work is named.  Second cause: see fail.  Third cause: a node with a node below it
      that was passed over for a node which is not complete*)
    fun above id =
      id :: (case the (Inttab.lookup (! parents) id) of SOME id' => above id' | NONE => []);
    val first_cause =
      Inttab.make_set
        (maps above
          (map (#id o #1) refused @
           map #id (filter (fn nd => exists (Termset.member named) (entries_at nd)) all_nodes)));
    fun third_cause incomplete =
      (case
        maps (above o #1) (filter (fn (_, first) => Inttab.defined incomplete first) (! skips))
        |> filter_out (Inttab.defined incomplete)
       of
        [] => incomplete
      | more => third_cause (fold Inttab.insert_set more incomplete));
    val incomplete = third_cause (Inttab.merge (K true) (first_cause, ! restricted));
    val capped = Inttab.defined first_cause (#id root_node);

    (*The set gets the parts of the fact and the concept facts of its first stage that are
      complete.  A piece named under no entry is not kept: nothing would come to it*)
    val passed_over = Inttab.make_set (map #1 (! skips));
    fun complete (nd: node) =
      not (#root nd) andalso member (op =) (above (#id nd)) (#id root_node) andalso
      (#stated nd orelse (case #leaf nd of Concept_Fact _ => true | _ => false)) andalso
      not (Inttab.defined incomplete (#id nd)) andalso not (Inttab.defined passed_over (#id nd));
    val ctxt2 =
      ctxt1 |> Destruction.map (fn {seen, ...} =>
        {seen =
           fold (fn nd: node => fn seen' =>
               if is_some (noted ctxt1 mask seen' (#key nd)) then seen'
               else add_note mask (#key nd, Not_Capped) seen')
             (filter complete all_nodes) seen,
         stopped = filter_out (Termset.is_empty o #names) stopped});

    (*the trace*)
    val show = Syntax.string_of_term ctxt1;
    fun prop_of ({thm, leaf, ...}: node) =
      (case leaf of Concept_Fact fact => Form.prop (Form.conclusion fact) | _ => Thm.prop_of thm);
    val _ = rev (! failures) |> List.app (fn (nd, reason, kept, class) =>
      trace ctxt1 (fn () =>
        failure_lines ctxt1 {internal = internal} (prop_of nd) reason kept
          (is_some (taken_by nd class))));
    val _ =
      (case (refused, limit) of
        (_ :: _, SOME n) =>
          trace ctxt1 (fn () =>
            ["concept extraction stopped the work on a fact: its count reached the limit of " ^
              string_of_int n ^ ".",
             "  fact: " ^ show (Thm.prop_of root)] @
            map_filter (fn (nd, Apply_Rules _) => SOME ("  not taken further: " ^ show (prop_of nd))
              | _ => NONE) refused @
            map_filter (fn (nd, Further_Work _) =>
                SOME ("  without its further work: " ^ show (prop_of nd))
              | _ => NONE) refused @
            map_filter (fn (nd, Take_Apart _) =>
                SOME ("  instance not taken apart: " ^ show (prop_of nd))
              | _ => NONE) refused)
      | _ => ());
  in {context = ctxt2, put = rev (! put), capped = capped} end;


(* a fact that comes in *)

(*A fact enters at a site.  Its key is looked up in the set (4A.4): a new fact is taken
  apart, and recorded with whether the limit has left work below it; a fact that is there
  is passed over.  In a context, a fact capped at a limit below the present one is taken
  apart again on what its context had before, at the present limit, and the outcome is merged
  into the context of now (4A.5).  It gives the entries put*)
fun destruct_fact own_variables ({safe_intro, masked_entries, ...}: destruct_work) site th0 ctxt =
  let
    val th = normal ctxt th0;
    val leaf = leaf_of ctxt th;
    val key = leaf_key th leaf;
    val show = Syntax.string_of_term ctxt;
    val limit =
      (case site of
        Theory_Level => NONE
      | Host_Premise => SOME 50
      | _ => SOME (Config.get ctxt extraction_limit));
    val mask = if masked_entries then SOME (mask_of th0) else NONE;
    fun traversal safe =
      traverse
       {limit = limit,
        two_groups = if site = Internal_Call then Concept_Check.Refused else Concept_Check.Aside,
        safe_intro = safe, mask = mask, recorder = key, own_variables = own_variables} th;
    fun set_status status = map_seen (add_note mask (key, status));

    fun first ctxt' =
      let
        val entries = contextual_part ctxt';
        val {seen, stopped} = Destruction.get ctxt';
        val {context = ctxt'', put, capped} = traversal safe_intro ctxt';
        val status =
          (case (capped, limit) of
            (true, SOME n) => Capped {limit = n, entries = entries, seen = seen, stopped = stopped}
          | _ => Not_Capped);
      in (put, set_status status ctxt'') end;

    (*the six points of the merge, 4A.5*)
    fun again {entries, seen, stopped} n ctxt' =
      let
        val {context = private, put, capped} =
          traversal safe_intro
            (ctxt' |> Context_Position.set_visible false |> put_contextual_part entries
              |> Destruction.put {seen = seen, stopped = stopped});
        val stopped' = #stopped (Destruction.get private);
        val recorded = filter_out (member same_stopped stopped) stopped';
        fun merge pieces =
          pieces
          (*what this fact had recorded and has not recorded again*)
          |> filter_out (fn piece =>
              #recorder piece aconv key andalso not (member same_stopped recorded piece))
          (*what was there before and has been begun*)
          |> filter_out (fn piece =>
              member same_stopped stopped piece andalso not (member same_stopped stopped' piece))
          |> fold (fn piece => fn pieces' =>
              if member same_stopped pieces' piece then
                pieces' |> map (fn piece' =>
                  if same_stopped (piece', piece) then add_names (#names piece) piece' else piece')
              else if member same_stopped stopped piece then pieces'
              else pieces' @ [piece]) stopped';
      in
        (put,
         ctxt'
         |> fold (#2 oo add_contextual) put
         (*the introduction rules of the traversal, which meets again those that are there*)
         |> safe_intro ? Classical.put_claset (Classical.claset_of private)
         |> map_stopped merge
         |> set_status
            (if capped then
              Capped {limit = n, entries = entries, seen = seen, stopped = stopped}
             else Not_Capped))
      end;
    val status =
      (case leaf of
        Concept_Fact fact => status_of ctxt mask fact
      | _ => noted ctxt mask (#seen (Destruction.get ctxt)) key);
  in
    (case (status, site, limit) of
      (NONE, _, _) => first ctxt
    | (SOME (Capped {limit = n, entries, seen, stopped}), In_Context, SOME n') =>
        if n' > n then
          (trace ctxt (fn () =>
            ["concept extraction takes a fact apart again: the limit stopped work below it at " ^
              string_of_int n ^ ", and the limit is now " ^ string_of_int n' ^ ".",
             "  fact: " ^ show (Thm.prop_of th)]);
           again {entries = entries, seen = seen, stopped = stopped} n' ctxt)
        else
          (trace ctxt (fn () =>
            ["concept extraction did not take a fact apart again: the limit stopped work \
              \below it at " ^ string_of_int n ^ ", and the limit is " ^ string_of_int n' ^ ".",
             "  fact: " ^ show (Thm.prop_of th)]);
           ([], ctxt))
    | _ => ([], ctxt))
  end;

(*f where the hypotheses of th0 are premises of the simplifier in force, as wherever what f
  writes for th0 is read; the simpset of the context is put back*)
fun with_premise th0 f ctxt =
  ctxt
  |> Simplifier.add_prems (map Thm.assume (Thm.chyps_of th0))
  |> f
  ||> Simplifier.put_simpset (Simplifier.simpset_of ctxt);

(*An internal call without masks starts without stopped work; the context that it gives back
  holds what the call recorded and not the outer work, and its caller drops it.  A call with
  masks, that of the handler of simp, takes each theorem apart where its premise is in force,
  starting without stopped work and leaving that of the context as it was: what the limit
  stops under a premise is not continued.  Where there is no limit the set starts empty, and
  that of the context is the same afterwards*)
fun destruct_facts own_variables (work as {masked_entries, ...}: destruct_work) site ths ctxt =
  if masked_entries then
    let
      fun one th ctxt' =
        let val {stopped, ...} = Destruction.get ctxt' in
          ctxt'
          |> map_stopped (K [])
          |> with_premise th (destruct_fact own_variables work site th)
          ||> map_stopped (K stopped)
        end;
    in fold_map one ths ctxt |>> flat end
  else
    let
      val outer = Destruction.get ctxt;
      val start =
        (case site of
          Internal_Call => map_stopped (K [])
        | Theory_Level => map_seen (K Termtab.empty)
        | _ => I);
      val finish = (case site of Theory_Level => map_seen (K (#seen outer)) | _ => I);
    in
      ctxt |> start |> fold_map (destruct_fact own_variables work site) ths |>> flat ||> finish
    end;

fun destruct_assms work site ths = #2 o destruct_facts [] work site ths;


(* the activation list of a concept *)

(*The list of a concept C is made at its declaration (2.3): what the statements of C give when
  they are taken apart without a limit, in a context that assumes C S.  That is the concept
  facts found, and what the lists of their concepts give.  Left out: a fact on S itself that C
  gives by its ancestors; the fact of a view, which the rule of the view gives; a fact on a
  structure where the list has a fact of a concept below*)
fun declare_activation name thy =
  let
    val {components, ...} = Concept_Package.the_concept thy name;
    val {context = ctxt0, S, ...} = Concept_Type.header_context thy name;
    val ([holds], ctxt) =
      Assumption.add_assumes
        [Thm.cterm_of ctxt0 (HOLogic.mk_Trueprop (Concept_Package.holds name S))] ctxt0;
    val statements = map (fn {kind, rule, ...} => (kind, elim_first ctxt rule holds)) components;
    val facts =
      destruct_facts [] {safe_intro = false, notation = false, masked_entries = false}
        Theory_Level (holds :: map #2 statements) ctxt
      |> #1 |> map #fact;
    val views =
      statements |> map_filter (fn (Concept_Package.View _, th) =>
          Option.map entry_prop (Form.of_thm ctxt th)
        | _ => NONE);
    fun plain fact = Thm.no_prems (Form.thm_of fact);
    fun on_structure fact fact' =
      Form.structure_term (Form.conclusion fact) aconv Form.structure_term (Form.conclusion fact');
    fun given fact =
      let val C = Form.concept (Form.conclusion fact) in
        Form.structure_term (Form.conclusion fact) aconv S andalso
        (C = name orelse is_some (Concept_Package.entailment thy name C))
      end;
    fun covered fact =
      facts |> exists (fn fact' =>
        plain fact' andalso on_structure fact fact' andalso
        is_some
          (Concept_Package.entailment thy (Form.concept (Form.conclusion fact'))
            (Form.concept (Form.conclusion fact))));
    val list =
      facts
      |> filter_out (fn fact =>
          plain fact andalso
          (given fact orelse member (op aconv) views (entry_prop fact) orelse covered fact))
      |> map Form.thm_of
      |> Proof_Context.export ctxt (Proof_Context.init_global thy)
      |> map (Thm.trim_context o Drule.zero_var_indexes);
  in Activation.map (Symtab.update (name, list)) thy end;

val _ =
  Theory.setup (Context.theory_map (Concept_Package.Declared.add 0 declare_activation));


(* what a declaration puts into the table *)

val plain = {safe_intro = false, notation = false, masked_entries = false};

(*The conclusion of th as a fact of a context made from ctxt: its term and type variables fixed;
  a premise concept u discharged where the hidden field of u is literally True, every other
  premise assumed and not noted, so that it is not taken apart*)
fun fact_context ctxt th =
  let
    val thy = Proof_Context.theory_of ctxt;
    val base = Concept_Type.base_name thy;
    val ((_, [th1]), ctxt1) = Variable.import true [Thm.transfer thy th] ctxt;
    fun held (\<^Const_>\<open>Trueprop for \<open>Const (c, _) $ u\<close>\<close>) =
          if c = base then Concept_Type.concept_holds ctxt1 u else NONE
      | held _ = NONE;
    val prems = Thm.prems_of th1;
    val assumptions = map (Thm.cterm_of ctxt1) (filter (is_none o held) prems);
    val ctxt2 = #2 (Assumption.add_assumes assumptions ctxt1);
    (*each assumption as the premise states it, not in the form of a fact of the context*)
    val assumed = map Thm.assume assumptions;
    fun proofs [] _ = []
      | proofs (p :: ps) hs =
          (case held p of SOME h => h :: proofs ps hs | NONE => hd hs :: proofs ps (tl hs));
  in (Drule.implies_elim_list th1 (proofs prems assumed), ctxt2) end;

(*the mark of an entry that a declaration stores without a mark given.  It stands in for the
  judgment at a declaration (2.3 of the search plan), which is not written*)
fun stored_safety th = if Thm.no_prems th then Safe_By_System else Unsafe;

(*What goes into the table of the theory with th, beside the entries of th itself: everything
  that th puts when it is taken apart in its fact_context, exported, with the premises of th.
  Left out: what th itself puts, which its declaration gives with its own marks; an entry
  whose structure is a schematic variable*)
fun activation_entries thy th =
  let
    val outer = Proof_Context.init_global thy;
    val (fact, ctxt) = fact_context outer th;
    val own = (case Form.of_thm ctxt fact of SOME f => entries_of ctxt f | NONE => []);
    val variables = Thm.fold_terms {hyps = true} Term.add_free_names fact [];
    val (put, ctxt') = destruct_facts variables plain Theory_Level [fact] ctxt;
  in
    put
    |> filter_out (fn {fact = f, ...}: registration => member (op aconv) own (entry_prop f))
    |> map (Form.thm_of o #fact)
    |> Proof_Context.export ctxt' outer
    |> map_filter (Form.of_thm outer o Drule.zero_var_indexes)
    |> filter (is_none o schematic_head o Form.conclusion)
    |> map (fn f =>
        {fact = f, user = false, safety = stored_safety (Form.thm_of f), mask = NONE,
         pos = Position.none}: registration)
  end;

type marks = {user: bool, safety: safety, pos: Position.T};

(*the entries of a rule itself, strengthened, with the marks of its declaration*)
fun own_entries ctxt ({user, safety, pos}: marks) fact =
  strengthened ctxt (fact, safety)
  |> map (fn (f, s) => {fact = f, user = user, safety = s, mask = NONE, pos = pos}: registration);

(*a rule in a theory: its own entries, and what it gives when it is taken apart; all computed
  on the theory that does not have the rule*)
fun rule_entries marks th thy =
  let val ctxt = Proof_Context.init_global thy in
    own_entries ctxt marks (the (Form.of_thm ctxt th)) @ activation_entries thy th
  end;

(*the rules of an import, or the fact of a view: one writing for all of them.  Without a mark
  given, a rule without premises is safe and one with premises unsafe*)
fun add_system_entries rules =
  register_theory (fn thy =>
    rules |> maps (fn {rule, safety} =>
      rule_entries
       {user = false, pos = Position.none,
        safety = the_default (stored_safety rule) safety} rule thy));

(*an instance: its rule goes in as it is, safe, and is not taken apart as a rule; its theorem
  from concept t to the declared concept is taken apart*)
fun add_instance_entries {rule, theorem} =
  register_theory (fn thy =>
    let val ctxt = Proof_Context.init_global thy in
      own_entries ctxt {user = false, safety = Safe_By_System, pos = Position.none}
        (the (Form.of_thm ctxt rule)) @
      activation_entries thy theorem
    end);

(*a fact that comes into a context: it is taken apart there, and each concept fact of its first
  stage that has no premises is a safe introduction rule of the context*)
fun take_in th =
  destruct_assms {safe_intro = true, notation = false, masked_entries = false} In_Context [th];

(*pos: where the attribute stands.  In a proof, and on an assumption of a statement, the
  attribute runs before the function on the indexed facts: it takes the rule in itself, and
  then puts the entries of the rule with the marks of the declaration.  Put first, they would
  hide the rule from what takes it apart*)
fun register_rule {safe} pos th context =
  if on_level context then context
  else
    let
      val fact = check_rule (Context.proof_of context) th;
      val marks = {user = true, safety = if safe then Safe_By_User else Unsafe, pos = pos};
    in
      (case context of
        Context.Theory thy => Context.Theory (register_theory (rule_entries marks th) thy)
      | Context.Proof ctxt =>
          let val ctxt' = take_in th ctxt in
            Context.Proof (fold (#2 oo add_contextual) (own_entries ctxt' marks fact) ctxt')
          end)
    end;

(*the attribute is defined on its whole source, which has the position of its name; Attrib.setup
  hands over the arguments alone*)
val _ =
  Theory.setup
    (Attrib.define_global \<^binding>\<open>concept_intro\<close>
      (fn src =>
        Attrib.attribute_syntax
          (Scan.lift (Scan.optional (Args.bang >> K true) false) >> (fn safe =>
            Thm.declaration_attribute
              (register_rule {safe = safe} (#2 (Token.name_of_src src))))) src)
      "declaring an introduction rule, used to prove that a structure is a concept" #> #2);



(** the lookup table **)

(*The facts of a context that are propositions of HOL, in the forms in which a condition may be
  written (4.3 of the plan of conditions), each form by its parts.  The table belongs to the
  package: its theorems are not noted, so the function on the indexed facts never meets them.
  Two facts are one where their propositions differ in the names of schematic variables only*)
structure Lookup = Proof_Data
(
  type T = thm Item_Net.T;
  fun init _ =
    Item_Net.init (op aconv o apply2 (canonical o Thm.prop_of)) (single o Thm.prop_of);
);

val lookup_table = Item_Net.content o Lookup.get;

(*A theorem of the proposition prop, which is in beta-eta normal form: an instance of a fact of
  the table.  Only the schematic variables of the fact are instantiated; those of prop stay*)
fun lookup_fact ctxt prop =
  let
    val thy = Proof_Context.theory_of ctxt;
    val i = Term.maxidx_of_term prop + 1;
    fun instance th0 =
      let val th = Thm.incr_indexes i th0 in
        try (Pattern.match thy (Thm.prop_of th, prop)) (Vartab.empty, Vartab.empty)
        |> Option.map (fn env => instance_of ctxt env th)
      end;
  in get_first instance (Item_Net.retrieve_matching (Lookup.get ctxt) prop) end;

(*the parts by which a form goes in: what open_fact gives of it, without True and without what
  is no proposition of HOL, as a part with premises*)
fun lookup_parts th =
  open_fact th |> filter (fn part =>
    (case Thm.prop_of part of
      \<^Const_>\<open>Trueprop for \<^Const_>\<open>True\<close>\<close> => false
    | \<^Const_>\<open>Trueprop for _\<close> => true
    | _ => false));

(*the first theorem of a proposition stays*)
fun add_part th table = if Item_Net.member table th then table else Item_Net.update th table;

(*the closing simpset of the simpset of a context, kept with that simpset: making one takes a
  deletion for each simproc of the package, and the facts of a context mostly come in under
  one simpset*)
structure Closing = Proof_Data
(
  type T = (simpset * Concept_Type.closing_simpset) option;
  fun init _ = NONE;
);

fun closing_simpset ctxt =
  let
    val ss = Simplifier.simpset_of ctxt;
    fun made () =
      let val closing = Concept_Type.closing_simpset ctxt ss
      in (closing, Closing.put (SOME (ss, closing)) ctxt) end;
  in
    (case Closing.get ctxt of
      SOME (ss', closing) => if pointer_eq (ss, ss') then (closing, ctxt) else made ()
    | NONE => made ())
  end;

(*The forms of a fact th after the one as written: th rewritten by the selector Simpset; that,
  or th where there is none, simplified once by the closing simpset.  A step that fails, as
  with a simproc of the user that fails, gives no form, like a simplification for which the
  steps do not suffice; nothing is said, and no error of it reaches the proof of the user.
  The schematic variables of th are fixed meanwhile*)
fun further_forms ctxt closing th =
  let
    val {context = ctxt', freeze, thaw_thm, ...} =
      Concept_Type.fix_schematics ctxt (Thm.prop_of th :: Thm.hyps_of th);
    fun step conv th' =
      Option.join (\<^try>\<open>conv (Thm.cprop_of th')\<close>)
      |> Option.map (fn eq => Thm.equal_elim eq th');
    val rewritten =
      if Concept_Type.may_rewrite ctxt (Thm.prop_of th) then
        step (SOME o (Concept_Type.selector_conv ctxt' then_conv Drule.beta_eta_conversion))
          (freeze th)
      else NONE;
    val simplified =
      step (Concept_Type.closing_rewrite ctxt' closing) (the_default (freeze th) rewritten);
  in map thaw_thm (the_list rewritten @ the_list simplified) end;

(*A fact that comes in enters the table by the parts of its forms, unless the table has every
  part of the fact as written: the same fact comes in more than once, and what is there is not
  simplified again.  A fact with premises has no part*)
fun enter_lookup th0 ctxt =
  let
    val th = normal ctxt th0;
    val written = lookup_parts th;
  in
    if forall (Item_Net.member (Lookup.get ctxt)) written then ctxt
    else
      let val (closing, ctxt') = closing_simpset ctxt in
        Lookup.map
          (fold add_part (written @ maps lookup_parts (further_forms ctxt' closing th))) ctxt'
      end
  end;



(** the facts that a context indexes **)

(*Proof_Context.Indexed_Facts hands over each fact that a context indexes by its proposition:
  the facts of a proof, the assumptions and notes of a statement or of an unnamed context, and
  what a block exports.  A theorem of the theory or of a level of a local theory is not
  indexed: it goes into the intro table by [concept_intro] only, and never enters the lookup
  table*)

(*whether assumption destruction may take something from a proposition, read without
  inference: it may say yes in vain, never no where there is work.  It reads the conclusion as
  the traversal does: through the conjunctions and universal quantifications that open_fact
  opens, a concept fact, or a proposition that an extraction rule takes.  Where the conclusion
  of that rule has a variable at its head, as in the rules that open an implication or a
  bounded quantification, what the rule takes out is read in turn, to a depth*)
fun has_work thy prop =
  let
    val rules = Extractions.get thy;
    (*the conclusion below the parameters and premises, the parameters as free variables*)
    fun hhf_concl t =
      Term.subst_bounds (rev (map Free (Logic.strip_params t)), Logic.strip_assums_concl t);
    (*what a rule takes out of P, with whether the head of its conclusion is a variable*)
    fun taken_out P ({rule, ...}: extraction) =
      let
        val (prem, rest) =
          Logic.dest_implies
            (Logic.incr_indexes ([], Term.maxidx_of_term P + 1) (Thm.prop_of rule));
      in
        (case (hhf_concl rest, try (Pattern.match thy (prem, P)) (Vartab.empty, Vartab.empty)) of
          (concl as \<^Const_>\<open>Trueprop for B\<close>, SOME env) =>
            SOME (is_Var (Term.head_of B), Envir.beta_norm (Envir.subst_term env concl))
        | _ => NONE)
      end;
    fun part depth \<^Const_>\<open>conj for A B\<close> = part depth A orelse part depth B
      | part depth \<^Const_>\<open>All T for P\<close> = part depth (Term.betapply (P, Free ("x", T)))
      | part depth A =
          let val P = HOLogic.mk_Trueprop (Envir.beta_eta_contract A) in
            is_some (dest_fact thy P) orelse
            Item_Net.retrieve_matching rules P |> exists (fn rule =>
              (case taken_out P rule of
                NONE => false
              | SOME (true, \<^Const_>\<open>Trueprop for B\<close>) => depth = 0 orelse part (depth - 1) B
              | SOME _ => true))
          end;
  in
    (case hhf_concl (Envir.beta_eta_contract prop) of
      \<^Const_>\<open>Trueprop for A\<close> => part 10 A
    | _ => false)
  end;

(*each theorem on its own; one that assumption destruction cannot take is passed over, so
  that no error of it reaches the proof of the user*)
fun take_facts ths ctxt =
  fold (fn th => fn ctxt' =>
      (case Exn.result (take_in th) ctxt' of
        Exn.Res ctxt'' => ctxt''
      | Exn.Exn exn =>
          (if Config.get ctxt' extraction_trace then
            tracing ("concept: the fact " ^ Thm.string_of_thm ctxt' th ^
              " is not taken apart:\n" ^ Runtime.exn_message exn)
           else ();
           ctxt')))
    ths ctxt;

(*What is done with the facts that come in.  Assumption destruction takes those that are not
  marked as handled and have work.  All of them enter the lookup table, after that: the
  selector Simpset rewrites them with the concept facts among them known*)
fun take_now ths ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    ctxt
    |> take_facts (filter (fn th => not (is_handled th) andalso has_work thy (Thm.prop_of th)) ths)
    |> fold enter_lookup ths
  end;

(*the facts of a statement that were kept while auto_concept_extraction was off, the latest
  first*)
structure Kept = Proof_Data
(
  type T = thm list;
  fun init _ = [];
);

val auto_extraction =
  Attrib.setup_config_bool \<^binding>\<open>auto_concept_extraction\<close> (K true);

(*what was kept, taken now in the order it came.  Nothing stays kept: a second call does
  nothing.  For a state whose goal was stated with the option off: on the context of the goal,
  before the first step of the proof*)
fun concept_extract ctxt =
  (case Kept.get ctxt of
    [] => ctxt
  | ths => ctxt |> Kept.put [] |> take_now (rev ths));

(*A fact of a proof body is taken at once.  A fact of a statement is too, unless
  auto_concept_extraction is off: then it is kept for concept_extract, and nothing is done
  with it before*)
fun take_indexed ths ctxt =
  if Variable.is_body ctxt orelse Config.get ctxt auto_extraction then take_now ths ctxt
  else Kept.map (fold cons ths) ctxt;

val _ = Theory.setup (Context.theory_map (Proof_Context.Indexed_Facts.add 0 take_indexed));



(** the premises that the simplifier assumes **)

(*Inside the selector Simpset (4A.6): a concept fact is strengthened and put with the mask of
  its premise, where the premise is in force; nothing is taken apart or activated, and a
  premise of another kind gives nothing*)
fun put_premise th0 =
  #2 o with_premise th0 (fn ctxt =>
    ((),
     (case leaf_of ctxt (normal ctxt th0) of
       Concept_Fact fact => #2 (put_strengthened (SOME (mask_of th0)) fact ctxt)
     | _ => ctxt)));

(*The handler of simp.  It gets a theorem with hypotheses: a part of a premise that the
  simplifier assumes, as the handlers of HOL have split it, or a rule that the user gives in a
  proof and that depends on an assumption.  It is taken apart with the mask of its hypotheses
  (inside the selector Simpset it is only put), and the rules that the simplifier makes of it by default are kept; for a rule of the user the
  simplifier drops what the handler did to the context, and the fact is mostly known already.
  A theorem without hypotheses, and one without work, is passed over: the simplifier goes on as
  without the handler*)
fun simp_handler ctxt th =
  if null (Thm.hyps_of th) orelse not (has_work (Proof_Context.theory_of ctxt) (Thm.prop_of th))
  then NONE
  else
    let
      val ctxt' =
        if Concept_Type.in_selector_simp ctxt then put_premise th ctxt
        else
          destruct_assms {safe_intro = false, notation = false, masked_entries = true}
            Internal_Call [th] ctxt;
    in SOME (Simplifier.get_mksimps_context ctxt' th ctxt') end;

val _ =
  Theory.setup (fn thy =>
    let
      val handler =
        ("concept",
          Simplifier.make_mksimps_handler
           {patterns = [HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT))], priority = ~1,
            kept_by_clear_simpset = false, handler = simp_handler});
    in
      thy
      |> Context.theory_map (Concept_Type.add_mksimps_handler handler #>
        Concept_Type.map_selector_simpset (Simplifier.add_mksimps_handler handler))
    end);

end;
