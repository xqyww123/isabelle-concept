(*  Title:      concept_fact.ML

The upper file of concept_fact: a derivation of the search replayed as a theorem; the entrance
for goals that must leave no condition, and the procedure of the selector Simpset on it; the
proof method concept_fact and its tactic; the attribute [[concept_fact "P"]], whose entrance
prove_proposition is that of the attribute of_concept too, and name_of, which prints that
attribute for a proposition; the decision on the host premise of an instance.  Not yet: the
simproc concept_fact, and the trigger of Sledgehammer.
*)

signature CONCEPT_FACT =
sig
  type derivation = Concept_Intro_Table.derivation
  val trace: bool Config.T
  val search: {max_distance: int option} -> Proof.context -> term ->
    derivation Concept_Intro_Table.result
  val prove: Proof.context -> derivation -> thm
  val unconditional_fact: Proof.context -> term -> thm option
  val concept_fact_tac: {max_distance: int option, warn_user_limit: bool} ->
    Proof.context -> int -> tactic
  val prove_proposition: Proof.context -> string * Position.T -> thm
  val name_of: Proof.context -> term -> string
  val host_premise: theory -> {host: term, conditions: term list} -> thm option
end;

structure Concept_Fact: CONCEPT_FACT =
struct

structure Intro = Concept_Intro_Table;

type derivation = Intro.derivation;

val trace = Concept_Type.trace;
val search = Concept_Search.search;



(** a derivation as a theorem **)

(* the terms and theorems of a derivation *)

fun map_derivation (f: term -> term) (g: thm -> thm) =
  let
    val eq = Option.map (Lazy.map g);
    fun goal (Intro.Goal {goal = A, form, solutions}) =
      Intro.Goal {goal = f A, form = eq form, solutions = map solution solutions}
    and solution (Intro.Solution {entry, rule, converted, premises}) =
      Intro.Solution
       {entry = entry, rule = Lazy.map g rule, converted = converted,
        premises = map premise premises}
    and premise (Intro.Concept {params, hyps, derivation}) =
          Intro.Concept
           {params = map (dest_Free o f o Free) params, hyps = map f hyps,
            derivation = goal derivation}
      | premise (Intro.Remaining {cond, simp}) =
          Intro.Remaining {cond = f cond, simp = eq simp};
  in goal end;


(* from the conditions to the goal *)

(*A from Trueprop (formula_of A)*)
fun prop_of_formula ctxt A th =
  Thm.equal_elim (Thm.symmetric (Intro.formula_conv ctxt (Thm.cterm_of ctxt A))) th;

(*the theorems of A1 ... An from that of A1 & (A2 & ... An), n > 0*)
fun conjuncts 1 th = [th]
  | conjuncts n th =
      let val (th1, th2) = HOLogic.conj_elim th in th1 :: conjuncts (n - 1) th2 end;

(*The goal of a derivation without schematic variables, from a theorem of its conditions as
  Intro.conditions_of gives them.  Every step takes its theorem as the derivation has it: the
  rule of a solution on the theorems of its premises, an equation backwards.  No step
  unifies*)
fun goal_thm ctxt (Intro.Goal {form, solutions, ...}) conditions =
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
      | cases [] _ = raise Fail "Concept_Fact.prove: a goal without a solution"

    and solution_thm (Intro.Solution {rule, premises, ...}) th =
      let
        val rule' = Lazy.force rule;
        val parts = if null premises then [] else conjuncts (length premises) th;
      in
        Drule.implies_elim_list rule'
          (@{map 3} premise_thm premises (Thm.prems_of rule') parts)
      end

    (*the premise of the rule as the rule has it, from the theorem of what it leaves*)
    and premise_thm (Intro.Remaining (condition as {simp, ...})) _ th =
          backwards simp (prop_of_formula ctxt (Intro.shown_condition condition) th)
      | premise_thm (Intro.Concept {params, hyps, derivation}) prem th =
          let
            (*what the premise leaves, under its parameters and hypotheses again*)
            val left =
              Logic.list_implies (hyps, HOLogic.mk_Trueprop (Intro.conditions_of derivation))
              |> fold_rev (Logic.all o Free) params;
            val under =
              fold (Thm.forall_elim o cterm o Free) params (prop_of_formula ctxt left th);
            (*the parameters and the hypotheses in the places that the premise has for them*)
            fun close (\<^Const_>\<open>Pure.all _ for \<open>Abs (_, _, A)\<close>\<close>) (x :: xs) hyps' =
                  Thm.forall_intr (cterm (Free x)) (close (Term.subst_bound (Free x, A)) xs hyps')
              | close (\<^Const_>\<open>Pure.imp for A B\<close>) xs hyps' =
                  Thm.implies_intr (cterm A) (close B xs (Thm.assume (cterm A) :: hyps'))
              | close _ _ hyps' =
                  goal_thm ctxt derivation (Drule.implies_elim_list under (rev hyps'));
          in close prem params [] end;
  in backwards form (cases solutions conditions) end;

(*R1 ==> ... ==> Rr ==> the goal of the derivation, as it was given to the search: the
  conditions that the search file hands to the user, and nothing else.  The schematic
  variables, those of the goal and those that the rules leave, are fixed while the theorem is
  made and come back as they were*)
fun prove ctxt derivation =
  let val tidied = Lazy.force (#proof (Concept_Search.tidy ctxt derivation)) in
    Concept_Type.fixing ctxt (Thm.prop_of tidied :: Intro.derivation_terms derivation)
      (fn ctxt' => fn freeze => fn fix =>
        let
          val tidied' = freeze tidied;
          val conditions = Thm.cprems_of tidied';
        in
          Drule.implies_elim_list tidied' (map Thm.assume conditions)
          |> goal_thm ctxt' (map_derivation fix freeze derivation)
          |> Drule.implies_intr_list conditions
        end)
  end;

fun unconditional_fact ctxt goal =
  Option.map (prove ctxt) (Concept_Search.search_unconditional ctxt goal);


(** the procedure of the selector Simpset for the conditions of its rules **)

(*a condition is a fact of the base concept.  It is searched without conditions in the context
  that the simplifier hands over, unchanged: there the search finds what the searches around
  this simplification tell it, and what it raises goes through to them*)
fun condition_proc ctxt ct =
  unconditional_fact ctxt (HOLogic.mk_Trueprop (Thm.term_of ct))
  |> Option.map (fn th => th RS @{thm Eq_TrueI});

val _ =
  Theory.setup (fn thy =>
    let
      val base = Concept_Type.base_name thy;
      val T = domain_type (Sign.the_const_type thy base);
      val simproc =
        Simplifier.make_simproc (Proof_Context.init_global thy)
          {name = "concept_condition", kind = Simplifier.Simproc,
           lhss = [Concept_Package.holds base (Var (("x", 0), T))],
           proc = K condition_proc, identifier = []};
    in
      Context.theory_map (Concept_Type.map_selector_simpset (Simplifier.add_proc simproc)) thy
    end);



(** a subgoal with its parameters and premises **)

(*a condition that is a premise of the subgoal as it stands is closed by that premise; the
  others stay, in their order.  Nothing is instantiated: a condition with a variable that a
  rule leaves is the user's to close*)
fun close_by_premises prems th =
  let
    fun close 0 th' = th'
      | close n th' =
          close (n - 1)
            (case find_first (fn prem => Thm.prop_of prem aconv Thm.prem_of th' 1) prems of
              SOME prem => Thm.implies_elim th' prem
            | NONE => Thm.permute_prems 0 1 th');
  in close (Thm.nprems_of th) th end;

(*The theorem lifted R1 ==> ... ==> lifted Rr ==> subgoal for a subgoal with parameters,
  premises and schematic variables (the five steps of 7.1 of the B plan, without the last).
  The premises of the subgoal are assumed and go through assumption destruction into a
  context of this call.  They close conditions only where close_by_premises is set: the
  subgoal is in HHF normal form, so the conditions are put into that form first, and those
  that are left come back in it.  Else a condition comes back as the search gives it.  It
  stands under the parameters and premises of the subgoal.  The variables of the subgoal come
  back as they were; those that the rules leave get indexes above maxidx, applied to the
  parameters where the conclusion does not have them.  The order of the steps is that of
  Subgoal.retrofit*)
fun prove_subgoal {max_distance, close_by_premises = closing, maxidx} ctxt subgoal
    : thm Intro.result =
  let
    val {context = ctxt1, fix, thaw_thm, ...} = Concept_Type.fix_schematics ctxt [subgoal];
    val ((params, body), ctxt2) =
      Variable.focus_cterm NONE (Thm.cterm_of ctxt1 (fix subgoal)) ctxt1;
    val asms = Drule.strip_imp_prems body;
    val prems = map Thm.assume asms;
    val ctxt3 =
      Intro.destruct_assms {safe_intro = false, notation = false, masked_entries = false}
        Intro.Internal_Call prems ctxt2;
  in
    (case Concept_Search.search {max_distance = max_distance} ctxt3
        (Thm.term_of (Drule.strip_imp_concl body)) of
      Intro.Failed failure => Intro.Failed failure
    | Intro.Found {value = derivation, cut_short} =>
        let
          val idx = maxidx + 1;
          val ps = map #2 params;
          (*the variables that the rules leave start from index 0, as those of a rule that the
            user applies*)
          val th =
            prove ctxt3 derivation
            |> closing ? (close_by_premises prems o Raw_Simplifier.norm_hhf ctxt3)
            |> Drule.zero_var_indexes;
          val ((rule_inst, th'), ctxt4) = Subgoal.lift_import idx ps th ctxt3;
          val (conditions, th'') = Subgoal.lift_subgoals ctxt4 params asms th';
          val rule =
            th''
            |> Drule.implies_intr_list asms
            |> Drule.forall_intr_list ps
            |> Drule.implies_intr_list conditions
            |> fold_rev (Thm.forall_intr o #1) rule_inst
            |> fold (Thm.forall_elim o #2) rule_inst
            |> thaw_thm
            |> Thm.adjust_maxidx_thm idx
            |> singleton (Variable.export ctxt4 ctxt1);
        in Intro.Found {value = rule, cut_short = cut_short} end)
  end;



(** what the user is told about the limit on user rules **)

fun uses n =
  "using concept_intro rules " ^ string_of_int n ^ (if n = 1 then " time" else " times");

fun increase n =
  "(increase it by \"declare [[concept_fact_user_limit = " ^ string_of_int (2 * n) ^ "]]\")";

fun gave_up ctxt =
  let val n = Config.get ctxt Concept_Search.user_limit
  in "gave up after " ^ uses n ^ " " ^ increase n end;

(*outputs: what the caller hands to the user*)
fun stopped_collecting ctxt outputs =
  let val n = Config.get ctxt Concept_Search.user_limit in
    "stopped collecting alternative solutions after " ^ uses n ^ ", so " ^ outputs ^
    " may not be the weakest and may thus be unprovable " ^ increase n
  end;



(** the proof method **)

(*The subgoal i by concept_fact: the conditions that are left become subgoals, under its
  parameters and premises.  No schematic variable of the state is instantiated.  The state is
  put into HHF normal form first, as Subgoal.focus does*)
fun concept_fact_tac {max_distance, warn_user_limit} ctxt i raw_st =
  let
    val st =
      raw_st |> Thm.solve_constraints |> Thm.transfer' ctxt
      |> Raw_Simplifier.norm_hhf_protect ctxt;
    fun warn text = if warn_user_limit then warning ("Tactic concept_fact " ^ text) else ();
  in
    if i < 1 orelse i > Thm.nprems_of st then Seq.empty
    else
      let val subgoal = Thm.term_of (Thm.cprem_of st i) in
        (case
          prove_subgoal
           {max_distance = max_distance, close_by_premises = false, maxidx = Thm.maxidx_of st}
            ctxt subgoal
         of
          Intro.Found {value = rule, cut_short} =>
            (if cut_short then
              warn (stopped_collecting ctxt "the proof obligations it outputs")
             else ();
             Thm.bicompose (SOME ctxt) {flatten = true, match = true, incremented = false}
               (false, rule, Thm.nprems_of rule - Logic.count_prems subgoal) i st)
        | Intro.Failed Intro.User_Limit => (warn (gave_up ctxt); Seq.empty)
        | Intro.Failed _ => Seq.empty)
      end
  end;

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>concept_fact\<close>
      (Scan.lift (Scan.option (Args.$$$ "distance" |-- Args.colon |-- Parse.nat)) >>
        (fn max_distance => fn ctxt =>
          SIMPLE_METHOD'
            (concept_fact_tac {max_distance = max_distance, warn_user_limit = true} ctxt)))
      "proof of a concept fact from the intro table");



(** the attribute concept_fact **)

(*a proposition is read and printed in the schematic mode, whatever the mode of the context: a
  schematic variable that the context binds, such as ?thesis, is its binding, any other is the
  proposition's own*)
val schematic = Proof_Context.set_mode Proof_Context.mode_schematic;

(*The proposition of a text: what a user writes, or what name_of prints at any of its levels.
  Where no reader reads it, the error is that of the system reader*)
fun read_prop ctxt text =
  (case Roundtrip_Syntax.read_prop (schematic ctxt) text of
    SOME prop => prop
  | NONE => Syntax.read_prop (schematic ctxt) text);

(*The text by which a proof refers to the theorem of a proposition: the attribute on the
  proposition, printed so that read_prop reads it back in this context.  A variable of the
  proposition that the context binds would be read as its binding, so such variables get
  indexes that neither the context binds nor the proposition has.  Where no text reads back,
  the text is the dummy fact, and the proof with it fails*)
fun name_of ctxt prop =
  let
    val binds = Variable.binds_of ctxt;
    val idx = Vartab.fold (Integer.max o #2 o #1) binds (Term.maxidx_of_term prop) + 1;
    fun apart (t as Var ((x, i), T)) =
          if Vartab.defined binds (x, i) then Var ((x, idx + i), T) else t
      | apart t = t;
  in
    (case Roundtrip_Syntax.string_of_prop (schematic ctxt) (Term.map_aterms apart prop) of
      SOME (_, text) => "[[concept_fact " ^ Symbol_Pos.quote_string_qq text ^ "]]"
    | NONE => "[[]]")
  end;

(*conditions ==> P for the proposition P of the text.  P is proved in its HHF normal form, as
  the proof method proves a subgoal, and comes back as it was written.  P may have premises:
  a condition is closed where its HHF normal form is one of them in the normal form of P, as it
  stands.  The schematic variables of P stay.  A condition that is left is in HHF normal form,
  under the parameters and premises of the normal form of P.  The theorem is proved in the
  context as it is, so it may have hypotheses*)
fun prove_proposition ctxt (text, pos) =
  let
    val prop = read_prop ctxt text;
    fun fail reason =
      error ("concept_fact could not prove " ^ quote (Syntax.string_of_term ctxt prop) ^
        Position.here pos ^ reason);
    (*P == its HHF normal form, which is what the proof method would get as a subgoal*)
    val hhf = Raw_Simplifier.rewrite_wrt ctxt true Drule.norm_hhf_eqs (Thm.cterm_of ctxt prop);
    val subgoal = Thm.term_of (Thm.rhs_of hhf);
  in
    (case
      prove_subgoal
       {max_distance = NONE, close_by_premises = true, maxidx = Term.maxidx_of_term prop}
        ctxt subgoal
     of
      Intro.Found {value, cut_short} =>
        (if cut_short andalso Context_Position.is_visible ctxt then
          warning
            ("concept_fact " ^ stopped_collecting ctxt "the premises of the theorem it returns")
         else ();
         (*behind the conditions that are left, P as it was written*)
         Conv.fconv_rule
           (Conv.concl_conv (Thm.nprems_of value - Logic.count_prems subgoal)
             (K (Thm.symmetric hhf))) value)
    | Intro.Failed Intro.No_Plan => fail ""
    | Intro.Failed Intro.User_Limit => fail (": it " ^ gave_up ctxt)
    | Intro.Failed Intro.Not_Concept_Goal =>
        fail
          (if null (Logic.strip_assums_hyp subgoal) then ": it is not a concept fact"
           else ": its conclusion is not a concept fact"))
  end;

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>concept_fact\<close>
      (Scan.lift (Parse.input Parse.embedded) >> (fn source =>
        Thm.rule_attribute [] (fn context => fn _ =>
          prove_proposition (Context.proof_of context)
            (Syntax.implode_input source, Input.pos_of source))))
      "the theorem of a proposition that concept_fact proves");



(** the host premise of an instance **)

(*w1 ==> ... ==> wn ==> C ?S where the conditions w1 ... wn that the user wrote give the host
  C S without leaving a condition; their variables come back schematic.  The context is made
  from the theory, so no fact of a context and no option of one decides*)
fun host_premise thy {host, conditions} =
  let
    val ctxt0 = Proof_Context.init_global thy;
    val ctxt = fold Proof_Context.augment (host :: conditions) ctxt0;
    val assumed = map (Thm.cterm_of ctxt) conditions;
    val ctxt' =
      fold (fn cond =>
        Intro.destruct_assms {safe_intro = false, notation = false, masked_entries = false}
          Intro.Host_Premise [Thm.assume cond]) assumed ctxt;
  in
    unconditional_fact ctxt' host
    |> Option.map
        (Drule.implies_intr_list assumed #> singleton (Variable.export ctxt ctxt0) #>
          Drule.zero_var_indexes)
  end;

end;
