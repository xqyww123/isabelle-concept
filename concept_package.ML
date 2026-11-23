(*  Title:      concept_package.ML

The command concept: its header, the predicate of a concept with its rules, and the named target
of its block.
*)

signature CONCEPT_PACKAGE =
sig
  type clause = (string * Position.T) list * string
  type item =
   {name: binding, typ: string, mixfix: mixfix, where_: (Position.T * clause list) option}
  type header =
   {args: (string * string option) list, name: binding, major: string option, items: item list,
    assumes: (Attrib.binding * (string * string list) list) list}
  val header: header parser
  datatype kind = Major of string | View of string * string | Edge of string | Plain
  type component = {kind: kind, name: Thm_Name.T option, rule: thm}
  type concept = {name: string, def: thm, components: component list, construction: thm}
  type entailment = {distance: int, entailment: thm, path: Thm_Name.T list option}
  val get_concept: theory -> string -> concept option
  val the_concept: theory -> string -> concept
  val entailment: theory -> string -> string -> entailment option
  val ancestors: theory -> string -> (string * entailment) list
  structure Declared: HOOKS where type arg = string and type state = theory
  type defined = {concept: string, binding: binding, mixfix: mixfix, lhs: term}
  structure Defined: HOOKS where type arg = defined and type state = local_theory
  val declare: header -> theory -> concept * theory
  val pretty_constants: theory -> header -> Pretty.T
end;

structure Concept_Package: CONCEPT_PACKAGE =
struct

(** the header **)

(* syntax *)

(*a where clause: the segments of its path, and its right-hand side*)
type clause = (string * Position.T) list * string;

(*what follows = in a header: the major parent, a type; then named items, each a field or a
  parent with a qualifier, which only its type tells apart; then the assumptions*)
type item =
 {name: binding, typ: string, mixfix: mixfix, where_: (Position.T * clause list) option};
type header =
 {args: (string * string option) list, name: binding, major: string option, items: item list,
  assumes: (Attrib.binding * (string * string list) list) list};

(*the approved text, at the token that does not fit*)
fun bad_syntax pos =
  cat_lines
   ["Bad syntax" ^ Position.here pos ^ ". The correct syntax of concept is:",
    "  concept 'a ordered_group = \"'a group\"",
    "    + ord: \"'a order\" where carrier = carrier",
    "    + norm :: \"'a \<Rightarrow> real\"",
    "    + assumes mono: \"x \<sqsubseteq>\<^bsub>ord\<^esub> y \<Longrightarrow> x * z \<sqsubseteq>\<^bsub>ord\<^esub> y * z\"",
    "The parent has no name; every field and every assumption has one"];

fun cut parser =
  Scan.!! (fn (toks: Token.T list, _) => fn () =>
    bad_syntax (case toks of tok :: _ => Token.pos_of tok | [] => Position.none)) parser;

(*a name without qualifier*)
val name =
  Parse.binding :|-- (fn b =>
    if Binding.is_empty b orelse Long_Name.is_qualified (Binding.name_of b) then Scan.fail
    else Scan.succeed b);

(*the segments of a path of identifiers, each with its position*)
val path =
  Parse.position (Parse.short_ident || Parse.long_ident) >> (fn (s, pos) =>
    let
      fun segments [] = []
        | segments syms =
            let val (seg, rest) = chop_prefix (fn (s, _) => s <> ".") syms in
              (Symbol_Pos.content seg, Position.range_position (Symbol_Pos.range seg)) ::
                segments (drop 1 rest)
            end;
    in segments (Symbol_Pos.explode (s, pos)) end);

val clause: clause parser = path --| Parse.$$$ "=" -- cut Parse.term;

val item: item parser =
  name --| (Parse.$$$ ":" || Parse.$$$ "::") -- cut Parse.typ -- Parse.opt_mixfix --
    Scan.option (Parse.position Parse.where_ -- cut (Scan.repeat1 clause))
  >> (fn (((b, T), mx), wh) =>
    {name = b, typ = T, mixfix = mx, where_ = Option.map (apfst #2) wh});

val assumption = name -- Parse.opt_attribs --| Parse.$$$ ":" -- cut (Scan.repeat1 Parse.propp);

(*each assumption is cut on its own: the one after "and" too*)
val assumes = Parse.$$$ "assumes" |-- Parse.and_list1 (cut assumption);

val header: header parser =
  cut Parse.type_args_constrained -- cut name --| cut (Parse.$$$ "=") --
  cut (item >> (fn it => (NONE, [it])) || Parse.typ >> (fn T => (SOME T, []))) --
  Scan.repeat (Parse.$$$ "+" |-- item) --
  Scan.optional (Parse.$$$ "+" |-- cut assumes) []
  >> (fn ((((args, b), (major, first)), items), asms) =>
    {args = args, name = b, major = major, items = first @ items, assumes = asms});


(* types *)

(*the concept that a type as it is written names, with its type arguments and, written as a
  scheme, its own more: a type abbreviation that is expanded would name the concept owning the
  type*)
fun dest_written thy (Type (c, Ts)) =
      if is_some (Concept_Type.get_info thy c) then SOME ((Ts, c), NONE)
      else
        (case (try (unsuffix "_scheme") c, try split_last Ts) of
          (SOME c', SOME (Ts', more)) =>
            if is_some (Concept_Type.get_info thy c') then SOME ((Ts', c'), SOME more) else NONE
        | _ => NONE)
  | dest_written _ _ = NONE;

(*the type of a concept from the items of its header: the first parent without a name is the
  major parent, a named item is a parent with a qualifier when its type names a concept, else a
  field*)
fun declare_type ({args, name = b, major, items, ...}: header) thy =
  let
    val ctxt0 = Proof_Context.init_global thy;
    val args' = map (apsnd (Typedecl.read_constraint ctxt0)) args;
    val ctxt = fold (Variable.declare_typ o TFree) args' ctxt0;
    val read = Proof_Context.read_typ_abbrev ctxt;
    val expand = Proof_Context.cert_typ ctxt;
    val parent =
      major |> Option.map (fn s =>
        let val T = read s in
          (case dest_written thy T of
            SOME ((Ts, c), NONE) => (map expand Ts, c)
          | _ =>
              error ("The parent type " ^ quote (Syntax.string_of_typ ctxt T) ^ " of concept " ^
                Binding.name_of b ^
                " must be a concept type without \"_scheme\", such as \"'a group\""))
        end);
    val items' =
      items |> map (fn {name = x, typ, mixfix, where_} =>
        let val T = read typ in
          (case (dest_written thy T, where_) of
            (SOME ((Ts, c), more), _) =>
              if Mixfix.is_empty mixfix then
                Concept_Type.View
                 {qualifier = x, parent = (map expand Ts, c),
                  more = the_default HOLogic.unitT (Option.map expand more),
                  where_ = these (Option.map #2 where_)}
              else error (bad_syntax (Mixfix.pos_of mixfix))
          | (NONE, NONE) => Concept_Type.Field (x, expand T)
          | (NONE, SOME (pos, _)) => error (bad_syntax pos))
        end);
    (*the sorts of the type parameters that the types determine*)
    val Ts =
      maps #1 (the_list parent) @
      maps (fn Concept_Type.Field (_, T) => [T]
        | Concept_Type.View {parent = (Ts, _), more, ...} => more :: Ts) items';
    val ctxt' = fold Variable.declare_typ Ts ctxt;
    val args'' = map (Proof_Context.check_tfree ctxt') args';
  in Concept_Type.declare {name = b, args = args'', parent = parent, items = items'} thy end;


(* assumptions *)

(*the assumptions as closed propositions over the structure S alone, with S.  They are read
  where S, the fields and the parents with a qualifier are variables: each is parsed and closed
  over its other free variables on its own, then all are checked together*)
fun read_assumptions thy name (assumes: (Attrib.binding * (string * string list) list) list) =
  let
    val cname = Long_Name.base_name name;
    val {context = ctxt, S, substitution} = Concept_Type.header_context thy name;
    fun at ((a, _): Attrib.binding) = quote (Binding.name_of a) ^ Position.here (Binding.pos_of a);
    val _ = assumes |> List.app (fn (_, props) =>
      if forall (null o #2) props then () else error "Illegal term bindings in context element");
    (*a name that comes again, with the assumption that used it first*)
    val _ =
      fold (fn (a, props) => fn seen =>
        (case AList.lookup (op =) seen (Binding.name_of (#1 a)) of
          SOME (first: Attrib.binding, props') =>
            error ("The name " ^ at a ^ " is already used by another assumption" ^
              Position.here (Binding.pos_of (#1 first)) ^ ": " ^
              space_implode " " (map (quote o Input.string_of o Syntax.read_input o #1) props'))
        | NONE => (Binding.name_of (#1 a), (a, props)) :: seen)) assumes [];
    val parsed = map (map (Syntax.parse_prop ctxt o #1) o #2) assumes;
    (*the concept has no predicate yet: its name would be closed as a variable*)
    val _ = (assumes ~~ parsed) |> List.app (fn ((a, _), props) =>
      if exists (fn prop => member (op =) (Variable.add_free_names ctxt prop []) cname) props then
        error ("The assumption " ^ at a ^ " uses " ^ quote cname ^
          " itself, which is a circular reference")
      else ());
    (*the type variables that the user wrote*)
    val written =
      (fold o fold o Term.fold_types o Term.fold_atyps)
        (fn TFree (a, _) => if String.isPrefix "'" a then insert (op =) a else I | _ => I)
        parsed [];
    val names = Variable.names_of ((fold o fold) Variable.declare_term parsed ctxt);
    val (parsed', _) = (fold_map o fold_map) Term.free_dummy_patterns parsed names;
    fun close prop =
      let val xs = rev (Variable.add_free_names ctxt prop [])
      in Logic.close_prop_constraint (Variable.default_type ctxt) (xs ~~ xs) [] prop end;
    val closed = (map o map) close parsed';
    val checked = unflat closed (Syntax.check_props ctxt (flat closed));
    (*a type variable that is no type parameter: written, or left by type inference*)
    val determined = Term.add_tfreesT (fastype_of S) [];
    val _ = (assumes ~~ checked) |> List.app (fn ((a, _), props) =>
      props |> List.app (fn prop =>
        (case subtract (op =) determined (Term.add_tfrees prop []) of
          [] => ()
        | extra =>
            (case filter (member (op =) written o #1) extra of
              [] =>
                error ("The assumption " ^ at a ^ " " ^
                  Undetermined_Types.message ctxt (Undetermined_Types.to_annotate determined prop))
            | named => Concept_Type.extra_type_variables cname named))));
    val export =
      Term.map_aterms (fn u as Free (x, _) => the_default u (AList.lookup (op =) substitution x)
        | u => u);
  in (S, map2 (fn (a, _) => fn props => (a, map export props)) assumes checked) end;


(** concepts **)

(*what a conjunct of the predicate's definition says*)
datatype kind =
  Major of string           (*this concept, the major parent, holds of the structure*)
| View of string * string   (*the parent with this qualifier, this concept, holds of its part*)
| Edge of string            (*an assumption D S: this concept holds of the structure*)
| Plain;                    (*any other assumption*)

(*name: the theorem of the fact where the declaration stores the rule, as the attributes of its
  assumption leave it; none for the rule to the base; rule: C ?S ==> ...*)
type component = {kind: kind, name: Thm_Name.T option, rule: thm};

(*def: C ?S == ...; components in the order of the definition; construction: ... ==> C ?S*)
type concept = {name: string, def: thm, components: component list, construction: thm};

(*from a concept to an ancestor: the number of steps, C ?S ==> A ?S, and the names of the rules
  of the steps, from C on, unless one of them has no name*)
type entailment = {distance: int, entailment: thm, path: Thm_Name.T list option};

fun map_concept f ({name, def, components, construction}: concept) : concept =
  {name = name, def = f def,
   components = components |> map (fn {kind, name, rule} =>
     {kind = kind, name = name, rule = f rule}),
   construction = f construction};

fun map_entailment f ({distance, entailment, path}: entailment) : entailment =
  {distance = distance, entailment = f entailment, path = path};

(*prefixes: by concept, the prefixes under which its facts are stored, each with the number of
  ancestors of the theory that stored facts under it.  Theorems are stored without their theory*)
structure Data = Theory_Data
(
  type T =
   {concepts: concept Name_Space.table, entailments: entailment Symtab.table Symtab.table,
    prefixes: (int * string) list Symtab.table};
  val empty =
   {concepts = Name_Space.empty_table "concept", entailments = Symtab.empty,
    prefixes = Symtab.empty};
  fun merge
     ({concepts, entailments, prefixes},
      {concepts = concepts', entailments = entailments', prefixes = prefixes'}) =
   {concepts = Name_Space.merge_tables (concepts, concepts'),
    entailments = Symtab.merge (K true) (entailments, entailments'),
    prefixes = Symtab.merge_list (op =) (prefixes, prefixes')};
);

val unnamed = Binding.name "unnamed";

(*a block of a concept stores its facts under the path of the concept, added to the naming of
  the theory*)
fun block_naming name = Name_Space.mandatory_path (Long_Name.base_name name);

(*the prefix of these names, with the number of ancestors of the theory; for a theory with its
  own naming, not that of a block*)
fun block_prefix thy name =
  (length (Context.ancestors_of thy),
    Long_Name.qualifier (Name_Space.full_name (block_naming name (Sign.naming_of thy)) unnamed));

fun get_concept thy name =
  Name_Space.lookup (#concepts (Data.get thy)) name |> Option.map (map_concept (Thm.transfer thy));

fun the_concept thy name =
  (case get_concept thy name of
    SOME concept => concept
  | NONE => error ("Unknown concept " ^ quote name));

(*the ancestors of a concept, the base included*)
fun ancestors thy name =
  these (Option.map Symtab.dest (Symtab.lookup (#entailments (Data.get thy)) name))
  |> map (apsnd (map_entailment (Thm.transfer thy)));

fun entailment thy name ancestor =
  Symtab.lookup (#entailments (Data.get thy)) name
  |> Option.mapPartial (fn tab => Symtab.lookup tab ancestor)
  |> Option.map (map_entailment (Thm.transfer thy));

(*a concept with a type of its own has the rule C.equality and the constants C.truncate and
  C.more*)
fun owns_type thy name = #owner (Concept_Type.the_info thy name) = name;

(*the approved text for the name a of a fact that the concept has by its declaration*)
fun already_bound ctxt cname a th =
  error ("The name " ^ quote a ^ " is already bound to the fact " ^ cname ^ "." ^ a ^ ": " ^
    Thm.string_of_thm ctxt th ^ "\nUse a different name");

(*run when a concept is declared, after its data are stored*)
structure Declared = Hooks(type arg = string type state = theory);


(** the predicate **)

(*the predicate of a concept is the constant of the concept's name; the base's is its selector*)
fun holds name t = Const (name, fastype_of t --> \<^Type>\<open>bool\<close>) $ t;

(*the n conjuncts of a right-nested conjunction*)
fun conjuncts 1 th = [th]
  | conjuncts n th = (th RS @{thm conjunct1}) :: conjuncts (n - 1) (th RS @{thm conjunct2});

(*the entailments of a new concept from the rules to its direct parents, in header order: the
  shorter way wins, among equals the earlier parent*)
fun entailments thy (steps: (string * Thm_Name.T option * thm) list) =
  let
    fun step (parent, name, rule) =
      (parent, {distance = 1, entailment = rule, path = Option.map single name}) ::
      (ancestors thy parent |> map (fn (ancestor, {distance, entailment, path}) =>
        (ancestor,
         {distance = distance + 1, entailment = rule RS entailment,
          path = (case (name, path) of (SOME a, SOME names) => SOME (a :: names) | _ => NONE)})));
    fun shorter (e: entailment, e': entailment) = if #distance e' < #distance e then e' else e;
  in
    fold (fn (ancestor, e) => Symtab.map_default (ancestor, e) (fn e' => shorter (e', e)))
      (maps step steps) Symtab.empty
  end;

(*the predicate of the declared concept b over the structure S, with its definition, its rules
  and its construction rule.  major: the concept of the major parent, which holds of S; views:
  the parents with a qualifier, each with its concept and its part of S; assumptions: closed
  propositions over S*)
fun define b S major (views: (string * string * term) list)
    (assumptions: (Attrib.binding * term list) list) thy =
  let
    val name = Sign.full_name thy b;
    val cname = Binding.name_of b;
    val base = Concept_Type.base_name thy;
    val ctxt = Proof_Context.init_global thy |> Variable.declare_term S;
    val head = holds name S;
    fun at (a: binding) = quote (Binding.name_of a) ^ Position.here (Binding.pos_of a);
    fun full a = Long_Name.append name a;

    (*the parents, the major one first: the name of the fact, none for the rule to the base;
      what the conjunct says; the concept that holds of the part of S*)
    val major_name = if major = base then NONE else SOME (Long_Name.base_name major);
    val parents =
      (major_name, Major major, holds major S) ::
      map (fn (q, P, t) => (SOME q, View (q, P), holds P t)) views;

    (* definition *)

    (*the propositions, each with the theorem of the fact of its assumption that it becomes*)
    val props =
      assumptions |> maps (fn ((a, _), ps) =>
        Thm_Name.make_list (full (Binding.name_of a), ps)
        |> map (fn (thm_name, prop) => (a, thm_name, prop)));
    (*an assumption as a formula of HOL, with the equation between the two*)
    fun atomized (a, _, prop) =
      let val eq = Object_Logic.atomize ctxt (Thm.cterm_of ctxt prop) in
        (case Thm.term_of (Thm.rhs_of eq) of
          \<^Const_>\<open>Trueprop for t\<close> => (t, eq)
        | _ =>
            error ("The assumption " ^ at a ^ " is not a formula of HOL: " ^
              quote (Syntax.string_of_term ctxt prop)))
      end;
    val atoms = map atomized props;
    val body = foldr1 HOLogic.mk_conj (map #3 parents @ map #1 atoms);
    val (def, thy1) = thy
      |> Sign.declare_const_global ((b, fastype_of S --> \<^Type>\<open>bool\<close>), NoSyn) |> #2
      |> Global_Theory.add_def (Thm.def_binding b, Logic.mk_equals (head, body));
    val ctxt1 = Proof_Context.init_global thy1 |> Variable.declare_term S;

    (* the conjuncts as rules C ?S ==> ... *)

    val holds_S = Thm.assume (Thm.cterm_of ctxt1 (HOLogic.mk_Trueprop head));
    val facts = conjuncts (length parents + length atoms) (rewrite_rule ctxt1 [def] holds_S);
    val (parent_facts, atom_facts) = chop (length parents) facts;
    fun global th =
      th |> Thm.implies_intr (Thm.cprop_of holds_S) |> Goal.norm_result ctxt1
      |> Drule.export_without_context;
    (*D S for a concept D: an edge*)
    fun edge prop =
      (case try HOLogic.dest_Trueprop prop of
        SOME (Const (D, _) $ t) =>
          if t aconv S andalso is_some (Concept_Type.get_info thy1 D) then SOME D else NONE
      | _ => NONE);
    val parent_components : component list =
      map2 (fn (a, kind, _) => fn th =>
        {kind = kind, name = Option.map (rpair 0 o full) a, rule = global th})
        parents parent_facts;
    val assumption_components : component list =
      @{map 3} (fn (_, thm_name, prop) => fn (_, eq) => fn th =>
        {kind = (case edge prop of SOME D => Edge D | NONE => Plain), name = SOME thm_name,
         rule = global (Thm.equal_elim (Thm.symmetric eq) th)})
        props atoms atom_facts;

    (* the truncate congruence rule of the predicate: C (P.truncate t) = C t *)

    val thy2 =
      (case Concept_Type.derive_truncate_cong ctxt1
          {const = Const (name, fastype_of S --> \<^Type>\<open>bool\<close>), def = def, position = 0} of
        SOME rule => thy1 |> Context.theory_map (Concept_Type.add_truncate_cong (name, 0) rule)
      | NONE => thy1);
    val ctxt2 = Proof_Context.init_global thy2 |> Variable.declare_term S;

    (* construction rule *)

    (*a parent holding of S itself is asked of S truncated to the parent's type, where its
      predicate ignores the truncation: the premise, and the conjunct from the premise*)
    fun on_structure P =
      let
        val t = Concept_Type.mk_truncate thy2 (#owner (Concept_Type.the_info thy2 P)) S;
        val plain = (HOLogic.mk_Trueprop (holds P S), I);
      in
        (case Concept_Type.selector_equation ctxt2 (holds P t) of
          SOME eq =>
            if Thm.nprems_of eq = 0 andalso
              #2 (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of eq))) aconv holds P S
            then (HOLogic.mk_Trueprop (holds P t), fn th => @{thm iffD1} OF [eq, th])
            else plain
        | NONE => plain)
      end;
    val premises =
      on_structure major ::
      map (fn (_, P, t) => (HOLogic.mk_Trueprop (holds P t), I)) views @
      map2 (fn (_, _, prop) => fn (_, eq) =>
        (case edge prop of
          SOME D => on_structure D
        | NONE => (prop, Thm.equal_elim eq))) props atoms;
    val construction =
      Goal.prove_global thy2 [#1 (dest_Free S)] (map #1 premises) (HOLogic.mk_Trueprop head)
        (*the premises as they are stated: the proof gets them with their outer quantifiers
          opened*)
        (fn {context = ctxt', ...} =>
          rewrite_goals_tac ctxt' [def] THEN
          resolve_tac ctxt'
            [foldr1 (fn (th, th') => @{thm conjI} OF [th, th'])
              (map (fn (prem, f) => f (Thm.assume (Thm.cterm_of ctxt' prem))) premises)] 1);

    (* facts *)

    (*the assumptions first, as their attributes leave them*)
    val (stored, thy3) = thy2
      |> Attrib.global_notes ""
        (map2 (fn ((a, atts), _) => fn cs =>
            ((Binding.qualify true cname a, atts), [(map #rule cs, [])]))
          assumptions (unflat (map #2 assumptions) assumption_components));
    (*the steps to the direct parents: the major parent, then the edges.  The fact of an edge
      names its step unless an attribute has made another theorem of it*)
    val edges =
      (assumption_components ~~ maps #2 stored) |> map_filter
        (fn ({kind = Edge D, name, rule}, th) =>
            SOME (D, if Thm.eq_thm_prop (rule, th) then name else NONE, rule)
          | _ => NONE);
    val {name = major_fact, rule = major_rule, ...} = hd parent_components;
    val table = entailments thy3 ((major, major_fact, major_rule) :: edges);
    val to_base = #entailment (the (Symtab.lookup table base));
    val equality =
      if owns_type thy3 name then
        Concept_Type.equality thy3 name |> Option.map (fn th =>
          ((Binding.qualify_name true b "equality", []), [([th OF [to_base, to_base]], [])]))
      else NONE;
    val parent_notes =
      map2 (fn (a, _, _) => fn {rule, ...}: component =>
        a |> Option.map (fn a' => ((Binding.qualify_name true b a', []), [([rule], [])])))
        parents parent_components;
    (*an assumption with the name of a fact that the concept has anyway*)
    val _ = assumptions |> List.app (fn ((a, _), _) =>
      (case find_first (fn ((a', _), _) => Binding.name_of a' = Binding.name_of a)
          (map_filter I parent_notes @ the_list equality) of
        SOME (_, (th :: _, _) :: _) =>
          already_bound (Proof_Context.init_global thy3) cname (Binding.name_of a) th
      | _ => ()));
    val concept : concept =
      {name = name, def = def, components = parent_components @ assumption_components,
       construction = construction};
    val thy4 = thy3
      |> Attrib.global_notes "" (map_filter I parent_notes @ the_list equality) |> #2
      |> Concept.add_predicate name name
      |> (fn thy' => thy' |> Data.map (fn {concepts, entailments, prefixes} =>
          {concepts =
             #2 (Name_Space.define (Context.Theory thy') true
               (b, map_concept Thm.trim_context concept) concepts),
           entailments =
             Symtab.update (name, Symtab.map (K (map_entailment Thm.trim_context)) table)
               entailments,
           prefixes = Symtab.insert_list (op =) (name, block_prefix thy' name) prefixes}));
  in (concept, Declared.invoke (Context.Theory thy4) name thy4) end;

(*the concept of a header: its type, then its predicate*)
fun declare (header as {name = b, assumes, ...}: header) thy =
  let
    val ({name, parent, views, ...}, thy1) = declare_type header thy;
    val assumes' =
      map (apfst (apsnd (map (Attrib.check_src (Proof_Context.init_global thy1))))) assumes;
    val (S, assumptions) = read_assumptions thy1 name assumes';
    val ctxt1 = Proof_Context.init_global thy1 |> Variable.declare_term S;
    val major = (case parent of SOME (_, P) => P | NONE => Concept_Type.base_name thy1);
    (*a parent with the name of a rule that the concept has anyway: that of the first parent,
      or equality where the concept has a type of its own*)
    fun reserved q =
      if is_some parent andalso q = Long_Name.base_name major then SOME "the base"
      else if q = "equality" andalso owns_type thy1 name then SOME "a fact"
      else NONE;
    val _ =
      #items header |> List.app (fn {name = x, ...}: item =>
        let val q = Binding.name_of x in
          (case (exists (fn {qualifier, ...} => qualifier = q) views, reserved q) of
            (true, SOME what) =>
              error ("You cannot name a field as " ^ quote q ^ Position.here (Binding.pos_of x) ^
                " as the name " ^ quote q ^ " is reserved for " ^ what ^ " of the concept " ^
                quote (Binding.name_of b))
          | _ => ())
        end);
    val qualified =
      views |> map (fn {name = c, qualifier, parent = (_, P), ...} =>
        (qualifier, P, Syntax.check_term ctxt1 (Const (c, dummyT) $ S)));
  in define b S major qualified assumptions thy1 end;


(** the block **)

(* the lookup chain *)

(*the order among the prefixes of one concept: that of a theory with more ancestors first, so a
  theory before those it imports; then by name*)
val sorted_prefixes = sort (prod_ord (rev_order o int_ord) string_ord) #> map #2;

fun stored_prefixes thy name = Symtab.lookup_list (#prefixes (Data.get thy)) name;

(*the prefixes that resolve a short name in the block of the concept: its own, that of the
  block first, which is there before the block stores a fact; then those of its ancestors, the
  nearer first*)
fun qualifiers thy name =
  let
    val base = Concept_Type.base_name thy;
    val chain =
      ancestors thy name |> filter_out (fn (a, _) => a = base)
      |> sort (int_ord o apply2 (#distance o #2)) |> map #1;
    val (_, own) = block_prefix thy name;
  in
    own :: remove (op =) own (sorted_prefixes (stored_prefixes thy name)) @
    maps (sorted_prefixes o stored_prefixes thy) chain
  end;


(* what a block fixes and assumes *)

(*the structure, and that the concept holds of it, with the name of this fact*)
fun elements thy name =
  let val S = Free ("\<S>", #scheme (Concept_Type.the_info thy name)) in
    {S = S, axioms = Binding.name (Long_Name.base_name name ^ "_axioms"),
     assumption = HOLogic.mk_Trueprop (holds name S)}
  end;


(* notes *)

(*the consumes of a rule counts premises from the front, the concept premises among them: with n
  premises put in front, a count that is there grows by n*)
fun shift_consumes n th =
  if AList.defined (op =) (Thm.get_tags th) "consumes"
  then Rule_Cases.add_consumes n th else th;

(*a theorem that re-declares a fact and depends on nothing but the assumption of the block, with
  that assumption made a premise again: it has no hyps and is stored as it is.  NONE for every
  other theorem, which takes the stock export*)
fun redeclared name lthy =
  if Local_Theory.redeclaring lthy then
    let val A = Thm.cterm_of lthy (#assumption (elements (Proof_Context.theory_of lthy) name)) in
      fn th =>
        let val hyps = Thm.chyps_of th in
          if null hyps then SOME th
          else if forall (fn h => h aconvc A) hyps then
            SOME (th |> Thm.implies_intr A |> Rule_Cases.save th |> shift_consumes 1)
          else NONE
        end
    end
  else K NONE;

(*a theorem to its local and its global form: the stock export makes each assumption of the
  context a premise; a theorem stored as it is takes the same export with the assumptions put
  aside, which only makes the fixed variables schematic.  A result just proved has all the
  assumptions as hyps or only those it uses, as its proof was forked or not*)
fun export redeclared (name_pos, th) lthy =
  (case redeclared th of
    SOME th' =>
      Local_Theory.global_form_result (Generic_Target.thm_definition (name_pos, th')) lthy
      |>> (fn (_, global) =>
        (Global_Theory.name_thm Global_Theory.unofficial2 name_pos th, Rule_Cases.save th' global))
  | NONE => Generic_Target.thm_definition (name_pos, th) lthy);

(*the entries that partial evaluation makes of each fact, in order: the declarations that it
  splits off, if any, then the entry with the binding of the fact*)
fun regroup facts evaluated =
  let
    fun close entry (pending, groups) =
      if Binding.is_empty (#1 (#1 entry)) then (entry :: pending, groups)
      else ([], rev (entry :: pending) :: groups);
    val ([], groups) = fold close evaluated ([], []);
    fun rebind ((b, _), _) group =
      let val (decls, (_, fact)) = split_last group in decls @ [((b, []), fact)] end;
  in map2 rebind facts (rev groups) end;

(*the facts that the declaration of a concept made, each with whether the system chose its
  name: equality and the rules of the parents; the user wrote the names of the assumptions*)
fun declared_facts thy name =
  (if owns_type thy name then [(Long_Name.append name "equality", true)] else []) @
  (#components (the_concept thy name) |> map_filter (fn {kind, name = thm_name, ...} =>
    thm_name |> Option.map (fn (a, _) =>
      (a, (case kind of Major _ => true | View _ => true | _ => false)))));

(*a fact of a block with the name of one that the declaration of the concept made.  With its
  very name: the approved error where the system chose the name; where the user wrote it,
  storing the fact reports the duplicate.  Under another prefix the new fact hides that of the
  declaration: a warning*)
fun check_fact_names name facts lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val declared = declared_facts thy name;
    val cname = Long_Name.base_name name;
  in
    facts |> List.app (fn ((b, _), _) =>
      let
        val a = Local_Theory.full_name lthy b;
        val a' = Long_Name.append name (Binding.long_name_of b);
      in
        (case AList.lookup (op =) declared a' of
          NONE => ()
        | SOME by_system =>
            if a = a' then
              if by_system then
                already_bound lthy cname (Binding.name_of b) (Global_Theory.get_thm thy a)
              else ()
            else if Context_Position.is_visible lthy then
              warning ("The theorem name " ^ quote (Binding.name_of b) ^
                Position.here (Binding.pos_of b) ^ " hides the existing fact " ^ cname ^ "." ^
                Binding.name_of b ^
                Position.here (Name_Space.the_entry_pos (Global_Theory.fact_space thy) a'))
            else ())
      end)
  end;

(*the facts of a block are stored in the theory in their global forms and bound nowhere else;
  the caller gets the local forms, as from the stock notes*)
fun notes name kind facts lthy =
  let
    val _ = check_fact_names name facts lthy;
    val thy = Proof_Context.theory_of lthy;
    (*the attributes once, in the block: those that change a theorem act on the statement as it
      is handed in; the others stay, for the theorem that is stored*)
    val groups =
      facts
      |> Attrib.map_thms (Goal.norm_result lthy)
      |> map (apfst (apfst (fn b => if Binding.is_empty b then unnamed else b)))
      |> Attrib.partial_evaluation lthy
      |> regroup facts;
    val export = export (redeclared name lthy);
    val (exported, lthy1) =
      (flat groups, lthy) |-> fold_map (fn (a, thms) => fn lthy' =>
        let val thms' = Thm_Name.expr (Local_Theory.full_name_pos lthy' (#1 a)) thms
        in lthy' |> fold_map (fn (args, atts) => fold_map export args #>> rpair atts) thms'
          |>> pair a end);
    val local_facts = Attrib.map_thms #1 exported;
    (*what the caller gets: the local forms with the remaining attributes applied, in a copy of
      the context that is dropped*)
    val local_results =
      #1 (Attrib.local_notes kind local_facts (Context_Position.not_really lthy1));
    val global_facts = Attrib.map_thms #2 exported;
    (*with the prefix of the block, for the lookup chain of later blocks*)
    val prefix = block_prefix thy name;
    val (stored, lthy2) =
      lthy1 |> Local_Theory.background_theory_result
        (Attrib.global_notes kind global_facts
          ##> Data.map (fn {concepts, entailments, prefixes} =>
            {concepts = concepts, entailments = entailments,
             prefixes = Symtab.insert_list (op =) (name, prefix) prefixes}));
    (*what the remaining attributes declare, at every level, for the theorems that are stored*)
    val declared = map (apfst (K Binding.empty_atts)) global_facts;
    val lthy3 = lthy2 |> Local_Theory.map_contexts (K (Attrib.local_notes kind declared #> #2));
    val results =
      unflat groups (map2 (fn (a, _) => fn (_, ths) => (a, ths)) stored local_results)
      |> map List.last;
  in (results, lthy3) end;


(* declaration *)

(*the standard morphism from the working context to a target context, the theory or a level of
  the block, except that a theorem that is stored as it is goes to every target in its global
  form: the one theorem that notes would store*)
fun block_morphism name lthy =
  if Local_Theory.redeclaring lthy then
    let
      val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy);
      val (as_it_is, _) =
        lthy |> Local_Theory.global_form_result (fn lthy' =>
          (Local_Theory.standard_morphism lthy' thy_ctxt, lthy'));
      val redeclared = redeclared name lthy;
    in
      fn ctxt =>
        let val phi = Local_Theory.standard_morphism lthy ctxt in
          Morphism.morphism "Concept_Package.block_morphism"
           {binding = [K (Morphism.binding phi)],
            typ = [K (Morphism.typ phi)],
            term = [K (Morphism.term phi)],
            fact = [K (map (fn th =>
              (case redeclared th of
                SOME th' => Rule_Cases.save th' (Morphism.thm as_it_is th')
              | NONE => Morphism.thm phi th)))]}
          |> Morphism.set_context' lthy
        end
    end
  else Local_Theory.standard_morphism lthy;

(*the data of a package go to the theory and to every level of the block, as in the stock theory
  target; they are not replayed when the block is opened again*)
fun declaration name (_: {syntax: bool, pervasive: bool, pos: Position.T}) decl lthy =
  let val phi = block_morphism name lthy in
    lthy
    |> Local_Theory.background_theory (Context.theory_map (fn context =>
        Morphism.form
          (Morphism.transform (phi (Proof_Context.init_global (Context.theory_of context))) decl)
          context))
    |> Local_Theory.map_contexts (fn _ => fn ctxt =>
        Context.proof_map (Morphism.form (Morphism.transform (phi ctxt) decl)) ctxt)
  end;


(* define and abbrev *)

type defined = {concept: string, binding: binding, mixfix: mixfix, lhs: term};

(*a constant that a block has defined or abbreviated: the concept, the binding and the mixfix as
  written, the constant applied to its parameters.  For those that give it a short name in the
  block and a dot access; without them the constant has its long name only*)
structure Defined = Hooks(type arg = defined type state = local_theory);

(*a concealed constant is internal to the package that defined it*)
fun defined name (b, mx) lhs lthy =
  if Name_Space.is_concealed (Proof_Context.const_space lthy) (#1 (dest_Const (head_of lhs)))
  then lthy
  else
    Defined.invoke (Context.Proof lthy) {concept = name, binding = b, mixfix = mx, lhs = lhs} lthy;

(*a concept with a type of its own has the constant truncate*)
fun check_constant name b lthy =
  if Binding.name_of b = "truncate" andalso owns_type (Proof_Context.theory_of lthy) name then
    error ("The constant name \"truncate\" is already bound to the constant " ^
      Long_Name.base_name name ^ ".truncate")
  else lthy;

(*the constant of the theory as in a theory target, but the levels of the block get no
  abbreviation for its short name, and the theory no mixfix: both are left to those that listen.
  The local name that the stock lifting binds lasts until the end of the command*)
fun foundation name (((b, U), mx), (b_def, rhs)) params =
  check_constant name b
  #> Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => defined name (b, mx) lhs #> pair (lhs, def));

fun target_abbrev name prmode (b, mx) global_rhs (_, term_params) =
  check_constant name b
  #> Local_Theory.background_theory_result (Sign.add_abbrev (#1 prmode) (b, global_rhs))
  #-> (fn (lhs, _) =>
    defined name (b, mx) (Term.list_comb (Logic.unvarify_global lhs, term_params)));


(* the target *)

fun target name : Named_Target.other_target =
  let
    val cname = Long_Name.base_name name;
    fun fixes S = let val (s, T) = dest_Free S in [(Binding.name s, SOME T, NoSyn)] end;
    fun setup thy =
      let val {S, axioms, assumption} = elements thy name in
        Proof_Context.init_global thy
        |> Variable.declare_term S
        |> Proof_Context.add_fixes (fixes S) |> #2
        |> Proof_Context.add_assms Assumption.assume_export
            [((axioms, [Classical.safe_intro NONE]), [(assumption, [])])] |> #2
        |> Proof_Context.put_default_fact_qualifiers (qualifiers thy name)
        |> Config.put Local_Theory.global_form_enabled true
      end;
    fun pretty lthy =
      let
        val thy = Proof_Context.theory_of lthy;
        val {S, axioms, assumption} = elements thy name;
        val ctxt = Proof_Context.init_global thy;
      in
        [Pretty.block (Pretty.keyword1 "concept" :: Pretty.brk 1 :: Pretty.str cname ::
          maps (fn elem => [Pretty.fbrk, Pretty.chunks (Element.pretty_ctxt ctxt elem)])
           [Element.Fixes (fixes S),
            Element.Assumes [((axioms, []), [(assumption, [])])]])]
      end;
    fun not_possible command hint _ =
      error (command ^ " cannot be used in concept " ^ cname ^ hint);
  in
    {naming = block_naming name,
     setup = setup,
     operations =
      {define = Generic_Target.define (foundation name),
       notes = notes name,
       abbrev = Generic_Target.abbrev (target_abbrev name),
       declaration = declaration name,
       theory_registration =
         not_possible "global_interpretation"
           ("\nUse interpretation instead, whose facts last until the end of this context, " ^
            "or write global_interpretation outside the concept"),
       locale_dependency =
         not_possible "sublocale"
           (": a concept is not a locale\n" ^
            "Use interpretation instead, whose facts last until the end of this context"),
       pretty = pretty}}
  end;

(*a name that a user writes for a target is first tried as the name of a concept*)
val _ =
  Theory.setup (Context.theory_map (Named_Target.Other_Target.add 0 (fn (thy, (xname, _)) =>
    fn NONE =>
        let
          val concepts = #concepts (Data.get thy);
          val name = Name_Space.intern (Name_Space.space_of_table concepts) xname;
        in if Name_Space.defined concepts name then SOME (target name) else NONE end
      | some => some)));


(* what a declaration prints *)

(*the constants of a new concept that a user can write: its predicate, its fields and its parents
  with a qualifier in the order of the header, and the two of a concept with a type of its own*)
fun pretty_constants thy ({name = b, items, ...}: header) =
  let
    val name = Sign.full_name thy b;
    val ctxt = Proof_Context.init_global thy;
    val consts =
      name :: map (fn {name = x, ...} => Long_Name.append name (Binding.name_of x)) items @
      (if owns_type thy name then map (Long_Name.append name) ["truncate", "more"] else []);
    fun line c =
      Pretty.block
       [Pretty.str "  ", Pretty.str (Proof_Context.extern_const ctxt c), Pretty.str " ::",
        Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ ctxt (Logic.unvarifyT_global (Sign.the_const_type thy c)))];
  in
    Pretty.chunks
      (Pretty.str ("Defined the new " ^ (case consts of [_] => "constant" | _ => "constants")) ::
        map line consts)
  end;


(** the command **)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>concept\<close> "declare a concept"
    (header -- Parse.opt_begin --| cut (Scan.ahead Parse.eof) >> (fn (header, begin) =>
      Toplevel.begin_main_target begin (fn thy =>
        let
          val ({name, ...}, thy') = declare header thy;
          val _ =
            if Config.get_global thy' Proof_Display.show_results
            then Pretty.writeln (pretty_constants thy' header) else ();
        in Named_Target.init_other [] (target name) thy' end)));

end;
