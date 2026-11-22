(*  Title:      concept_type.ML

The concept types.  A value of a concept type holds all parameters of a concept.  Every concept
with leaves of its own adds a layer: a typedef over a balanced tuple of its leaves and the more
slot.  All chains start at the base concept "concept", whose single bool leaf is read by the
predicate concept.  A parent with a qualifier is a view: its leaves not given by "where" are
stored as anonymous leaves, and the view constant rebuilds its value.  An anonymous leaf is read
only through the view holding it.  The names that expose the representation (Abs, Rep, the
definitions) cannot be reached by any input.  Proofs inside rewrite with fixed rules
only.  A selector simproc synthesizes the equations of the selectors on instances, views and
truncate.  The selector Simpset rewrites with these simprocs and with no rule of the theory's
simpset; as in simp, what its congruence rules assume (P in P --> Q, x : A under a bounded
quantifier) rewrites the other side.  It is used through put_selector_simpset only.
*)

signature CONCEPT_TYPE =
sig
  type parent = typ list * string
  type view = {name: string, qualifier: string, parent: parent, concept_eq: thm}
  type info =
   {name: string, args: (string * sort) list, parent: parent option, owner: string,
    scheme: typ, more: term, views: view list}
  datatype source_kind = Family | Super
  type source =
   {kind: source_kind, layer: string, term: term, fields: thm, forward: thm option}
  type instance =
   {name: string, const: term, concept: parent, params: term list, constraint: term,
    concept_eq: thm, family: string option, source: source option}
  val base_name: theory -> string
  val get_info: theory -> string -> info option
  val the_info: theory -> string -> info
  val get_instance: theory -> string -> instance option
  val equality: theory -> string -> thm option
  val truncate_eq: Proof.context -> {concept: string, s: term, t: term} ->
    {env: Type.tyenv * Envir.tenv, eq: thm lazy, extra: term option, reached: bool} option
  val add_implication: string -> thm -> theory -> theory
  val super_param: theory -> string -> int option
  val linked_keys: theory -> string -> string list
  type covering = {layer: string, member: string, exact: bool}
  val own_layer: theory -> {family: string, concept: string} -> string * covering option
  val covered_layer: theory -> {family: string, concept: string} -> covering option
  val dest_scheme_type: theory -> typ -> (string * typ list * typ) option
  datatype cong_rule = Congruence of thm | Commutes of {owner: string, def: thm}
  val truncate_cong: Context.generic -> string * int -> cong_rule option
  val add_truncate_cong: string * int -> cong_rule -> Context.generic -> Context.generic
  val derive_truncate_cong: Proof.context -> {const: term, def: thm, position: int} ->
    cong_rule option
  val put_selector_simpset: Proof.context -> Proof.context
  val map_selector_simpset: (Proof.context -> Proof.context) -> Context.generic -> Context.generic
  val selector_equation: Proof.context -> term -> thm option
  val source_equation: Proof.context -> term -> thm option
  datatype item =
    Field of binding * typ
  | View of {qualifier: binding, parent: parent, more: typ,
      where_: ((string * Position.T) list * string) list}
  val declare_base: theory -> theory
  val declare: {name: binding, args: (string * sort) list, parent: parent option,
    items: item list} -> theory -> info * theory
  val define_instance: Proof.context ->
    {family: string option, name: binding, define: bool, concept: parent, params: term list,
     where_: ((string * Position.T) list * string) list, constraint: term} ->
    theory -> instance * theory
end;

structure Concept_Type: CONCEPT_TYPE =
struct

(** data **)

type parent = typ list * string;

(*acc: the selector constant of a named leaf, a lambda term over the scheme for an anonymous
  one; conv: acc applied to the canonical term = the leaf's argument*)
type leaf = {name: string option, typ: typ, acc: term, conv: thm};

type layer =
 {ext: string,  (*the extension type constructor*)
  abs: term, leaves: leaf list, more_conv: thm,
  defs: thm list,  (*the definitions of the selectors and of more*)
  abs_inverse: thm,  (*Rep (Abs x) = x*)
  rep_inject: thm,  (*(Rep x = Rep y) = (x = y)*)
  equality: thm, surjective: thm, truncate: term, truncate_def: thm, truncate_conv: thm};

(*a leaf of a view's parent: the leaf of the declaring concept that it is, or a value given by
  the declaring concept's where clause that is no leaf (the declaring concept, the value)*)
datatype slot = Leaf of int | Given of string * term;

(*const: at the declaring concept's own type arguments; parent and more, the type of the more
  slot of the view's values: at the same; slots: one per leaf of the parent, and one for the
  more slot unless more is unit; values: the definition's value of each slot, in the variable
  S; concept_eq: concept (C.q S) = True*)
type view_entry =
 {name: string, qualifier: string, const: term, parent: parent, more: typ,
  slots: slot list, S: term, values: term list, def: thm, concept_eq: thm};

(*owner: the concept owning the type (itself if it has a layer);
  scheme: the type of the values, the more slot a type variable;
  more: the more selector of the owner, at type scheme => more slot;
  views: the concept's own views, in header order*)
type entry =
 {name: string, args: (string * sort) list, parent: parent option, owner: string,
  layer: layer option, scheme: typ, more: term, views: view_entry list};

datatype source_kind = Family | Super;

(*where an instance c xs takes its layers up to layer from: the member of its family owning
  that layer (Family), or the t of "where super = t" (Super); term: over the parameters xs;
  fields: concept.more (layer.truncate (c ?xs)) = concept.more (layer.truncate term);
  forward: concept (c ?xs) ==> concept term*)
type source =
 {kind: source_kind, layer: string, term: term, fields: thm, forward: thm option};

(*an instance constant applied to its parameters: the value of each leaf, more, and the base's
  leaf (True, or the conjunction of the if clauses); wholes: the views given as a whole, each by
  the view constants from the instance outward, with the value; concept_eq: concept (x params) =
  constraint; implications: concept (x ?params) ==> concept ?param, by the parameter's position*)
type instance_entry =
 {name: string, const: term, concept: parent, params: term list, values: term list,
  more: term, wholes: (string list * term) list, constraint: term, def: thm, concept_eq: thm,
  family: string option, source: source option, implications: thm Inttab.table};

(*the theorems of what is stored: stored without their theory, handed out in the theory that
  asks*)
fun map_layer_thms f
    ({ext, abs, leaves, more_conv, defs, abs_inverse, rep_inject, equality, surjective, truncate,
      truncate_def, truncate_conv}: layer) : layer =
  {ext = ext, abs = abs,
   leaves =
    map (fn {name, typ, acc, conv} => {name = name, typ = typ, acc = acc, conv = f conv}) leaves,
   more_conv = f more_conv, defs = map f defs, abs_inverse = f abs_inverse,
   rep_inject = f rep_inject, equality = f equality, surjective = f surjective,
   truncate = truncate, truncate_def = f truncate_def, truncate_conv = f truncate_conv};

fun map_view_thms f
    ({name, qualifier, const, parent, more, slots, S, values, def, concept_eq}: view_entry)
    : view_entry =
  {name = name, qualifier = qualifier, const = const, parent = parent, more = more,
   slots = slots, S = S, values = values, def = f def, concept_eq = f concept_eq};

fun map_entry_thms f ({name, args, parent, owner, layer, scheme, more, views}: entry) : entry =
  {name = name, args = args, parent = parent, owner = owner,
   layer = Option.map (map_layer_thms f) layer, scheme = scheme, more = more,
   views = map (map_view_thms f) views};

fun map_instance_thms f
    ({name, const, concept, params, values, more, wholes, constraint, def, concept_eq, family,
      source, implications}: instance_entry) : instance_entry =
  {name = name, const = const, concept = concept, params = params, values = values, more = more,
   wholes = wholes, constraint = constraint, def = f def, concept_eq = f concept_eq,
   family = family,
   source =
    Option.map (fn {kind, layer, term, fields, forward} =>
      {kind = kind, layer = layer, term = term, fields = f fields,
       forward = Option.map f forward}) source,
   implications = Inttab.map (K f) implications};

(*base: the base concept; owners: extension type ~> the concept owning it*)
structure Data = Theory_Data
(
  type T =
   {base: string option, entries: entry Symtab.table, owners: string Symtab.table,
    instances: instance_entry Symtab.table};
  val empty =
    {base = NONE, entries = Symtab.empty, owners = Symtab.empty, instances = Symtab.empty};
  fun merge
    ({base, entries, owners, instances},
     {base = base', entries = entries', owners = owners', instances = instances'}) =
    {base = if is_some base then base else base',
     entries = Symtab.merge (K true) (entries, entries'),
     owners = Symtab.merge (K true) (owners, owners'),
     instances = Symtab.merge (K true) (instances, instances')};
);

fun map_data f =
  Data.map (fn {base, entries, owners, instances} =>
    let val (base', entries', owners', instances') = f (base, entries, owners, instances)
    in {base = base', entries = entries', owners = owners', instances = instances'} end);

fun base_name thy =
  (case #base (Data.get thy) of
    SOME name => name
  | NONE => error "The base concept is not declared");

fun get_entry thy =
  Option.map (map_entry_thms (Thm.transfer thy)) o Symtab.lookup (#entries (Data.get thy));

fun the_entry thy name =
  (case get_entry thy name of
    SOME entry => entry
  | NONE => error ("Unknown concept " ^ quote name));

fun put_entry (entry as {name, layer, ...}: entry) =
  map_data (fn (base, entries, owners, instances) =>
    (base, Symtab.update (name, map_entry_thms Thm.trim_context entry) entries,
     (case layer of
       SOME {ext, ...} => Symtab.update (ext, name) owners
     | NONE => owners),
     instances));

fun add_view view name thy =
  let val {args, parent, owner, layer, scheme, more, views, ...} = the_entry thy name in
    put_entry {name = name, args = args, parent = parent, owner = owner, layer = layer,
      scheme = scheme, more = more, views = views @ [view]} thy
  end;

fun get_instance_entry thy =
  Option.map (map_instance_thms (Thm.transfer thy)) o Symtab.lookup (#instances (Data.get thy));

fun put_instance (instance as {name, ...}: instance_entry) =
  map_data (fn (base, entries, owners, instances) =>
    (base, entries, owners,
     Symtab.update (name, map_instance_thms Thm.trim_context instance) instances));


(* families *)

(*the member of a family that later members take a layer from; shown: its name as declared;
  theory: where it is defined; layers: those of its type, from the last toward the base*)
type provider =
  {member: string, shown: string, theory: string, pos: Position.T, layers: string list};

(*family ~> the concept owning a layer ~> the provider of that layer.  Theories can be merged
  when they agree on the provider of every layer*)
structure Families = Theory_Data'
(
  type T = provider Symtab.table Symtab.table;
  val empty = Symtab.empty;
  fun merge (args: (theory * T) list) =
    let
      val keys =
        fold (fn (_, tab) => Symtab.fold (fn (family, layers) =>
          fold (fn layer => insert (op =) (family, layer)) (Symtab.keys layers)) tab) args [];
      (*the theories with a provider of the layer, each with it*)
      fun users (family, layer) =
        args |> map_filter (fn (thy, tab) =>
          Symtab.lookup tab family
          |> Option.mapPartial (fn layers => Symtab.lookup layers layer)
          |> Option.map (pair (Context.theory_base_name thy)));
      (*a layer with several providers: the family with the last layer that these have in
        common, how many layers they have in common, and the theories with their providers*)
      fun conflict (key as (family, _)) =
        let
          val used = users key;
          val members = distinct (op = o apply2 #member) (map #2 used);
        in
          (case members of
            {layers, ...} :: _ :: _ =>
              let
                val common =
                  filter (fn l => forall (fn p: provider => member (op =) (#layers p) l) members)
                    layers;
              in SOME ((family, hd common), (length common, used)) end
          | _ => NONE)
        end;
      (*one conflict for each such last layer, the nearer to the base the later*)
      val conflicts =
        fold (fn key =>
          (case conflict key of
            SOME (part, (depth, used)) =>
              AList.map_default (op =) (part, (depth, []))
                (apsnd (union (eq_fst (op =)) used))
          | NONE => I)) keys []
        |> sort (prod_ord string_ord (rev_order o int_ord) o
            apply2 (fn ((family, _), (depth, _)) => (family, depth)));
      val theories = map (Context.theory_base_name o #1) args;
      fun in_order names = filter (member (op =) names) theories;
      fun listed names =
        let val (front, last) = split_last names
        in commas_quote front ^ " and " ^ quote last end;
      fun importing names =
        if length names = 2 then "both " ^ listed names ^ " import"
        else listed names ^ " all import";
      fun part ((family, layer), _) =
        "the " ^ Long_Name.base_name layer ^ " part of the family " ^ family;
      fun base ((family, layer), _) = family ^ "." ^ Long_Name.base_name layer;
      fun uses indent (_, (_, used)) =
        in_order (map #1 used) |> map (fn name =>
          let val {shown, pos, theory, ...}: provider = the (AList.lookup (op =) used name) in
            indent ^ quote name ^ " uses " ^ shown ^ Position.here pos ^ " defined in " ^
              quote theory
          end);
      val names = in_order (maps (map #1 o #2 o #2) conflicts);
      fun cannot what = "Cannot merge theories " ^ listed names ^ ": they disagree on " ^ what;
    in
      (case conflicts of
        [] =>
          fold (fn (_, tab) => fn tab' => Symtab.join (K (Symtab.merge (K true))) (tab', tab))
            args empty
      | [c] =>
          error (cat_lines
            ([cannot (part c)] @ uses "  " c @
              ["You must define " ^ base c ^ " in a theory that " ^ importing names ^
                ", to serve as the common base"]))
      | cs =>
          error (cat_lines
            ([cannot (string_of_int (length cs) ^ " parts of " ^
                (case distinct (op =) (map (#1 o #1) cs) of
                  [family] => "the family " ^ family
                | _ => "families"))] @
              maps (fn c => ("  " ^ part c ^ " (common base: " ^ base c ^ ")") :: uses "    " c)
                cs @
              ["You must define each common base in a theory that " ^ importing names])))
    end;
);

fun providers thy family = the_default Symtab.empty (Symtab.lookup (Families.get thy) family);

(*the keys linked by "where super = t": that of the instance and that of the head of t*)
structure Links = Theory_Data
(
  type T = string list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge_list (op =);
);


(* what other packages see *)

type view = {name: string, qualifier: string, parent: parent, concept_eq: thm};

type info =
 {name: string, args: (string * sort) list, parent: parent option, owner: string,
  scheme: typ, more: term, views: view list};

type instance =
 {name: string, const: term, concept: parent, params: term list, constraint: term,
  concept_eq: thm, family: string option, source: source option};

fun info_of ({name, args, parent, owner, scheme, more, views, ...}: entry) : info =
  {name = name, args = args, parent = parent, owner = owner, scheme = scheme, more = more,
   views = map (fn {name, qualifier, parent, concept_eq, ...} =>
     {name = name, qualifier = qualifier, parent = parent, concept_eq = concept_eq}) views};

fun instance_of
    ({name, const, concept, params, constraint, concept_eq, family, source, ...}: instance_entry)
    : instance =
  {name = name, const = const, concept = concept, params = params, constraint = constraint,
   concept_eq = concept_eq, family = family, source = source};

fun get_info thy = Option.map info_of o get_entry thy;
val the_info = info_of oo the_entry;
fun get_instance thy = Option.map instance_of o get_instance_entry thy;


(* the constants the selector simproc knows *)

datatype const_kind =
  Leaf_Sel of int  (*a named leaf: its index among the leaves of every concept having it*)
| More_Sel of string  (*the more of the layer of this concept*)
| View_Const of string  (*a view, declared by this concept*)
| Truncate of string  (*the truncate of the layer of this concept*)
| Predicate;  (*the base's predicate*)

structure Kinds = Theory_Data
(
  type T = const_kind Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

fun get_kind thy = Symtab.lookup (Kinds.get thy);


(** terms and types **)

(*apply a stored term f (type variables as TFree) to x, instantiating the type of f by matching
  its domain against the type of x*)
fun app thy f x =
  let
    val f' = Logic.varify_types_global f;
    val tyenv = Sign.typ_match thy (domain_type (fastype_of f'), fastype_of x) Vartab.empty;
  in Envir.beta_norm (Envir.subst_term_types tyenv f' $ x) end;

(*instantiate stored terms (type variables as TFree) at the types making const's type T*)
fun matcher thy const T =
  let val tyenv = Sign.typ_match thy (Logic.varifyT_global (fastype_of const), T) Vartab.empty
  in Envir.subst_term_types tyenv o Logic.varify_types_global end;

fun const_of thy c = Const (c, Logic.unvarifyT_global (Sign.the_const_type thy c));

fun subst_args thy (Ts, name) =
  Term.typ_subst_atomic (map TFree (#args (the_entry thy name)) ~~ Ts);

(*a fresh type variable for the more slot*)
fun more_var used = (singleton (Name.variant_list used) "'\<e>", \<^sort>\<open>type\<close>);

(*the type of the values of a concept at type arguments Ts, with more type M*)
fun scheme_type thy (Ts, name) M =
  let val {args, scheme, more, ...} = the_entry thy name in
    Term.typ_subst_atomic ((range_type (fastype_of more), M) :: (map TFree args ~~ Ts)) scheme
  end;

fun unit_type thy p = scheme_type thy p HOLogic.unitT;


(*the concepts along the major chain of a concept at type arguments Ts, the base first*)
fun major_chain thy (p as (_, name)) =
  (case #parent (the_entry thy name) of
    NONE => [p]
  | SOME (Us, q) => major_chain thy (map (subst_args thy p) Us, q) @ [p]);

fun the_layer thy name = the (#layer (the_entry thy name));

(*the layers along the chain, the base first: the concept owning each, with its leaf types*)
fun chain thy p =
  major_chain thy p |> map_filter (fn p' as (_, name) =>
    Option.map (fn {leaves, ...} => (name, map (subst_args thy p' o #typ) leaves))
      (#layer (the_entry thy name)));

(*the next layer toward the base*)
fun layer_below thy layer =
  Option.map (#owner o the_entry thy o #2) (#parent (the_entry thy layer));

(*a layer and those toward the base*)
fun layers_from thy layer =
  layer :: (case layer_below thy layer of SOME below => layers_from thy below | NONE => []);

(*a leaf of the values of a concept: typ at the actual types; acc as stored, at the owner's own
  types (apply it with app); owner: the concept whose layer has it*)
type flat_leaf = {name: string option, typ: typ, acc: term, owner: string};

(*the leaves of the values of a concept at type arguments Ts, root first, without the base's;
  a leaf has the same index in every concept whose values have it*)
fun flat_leaves thy p : flat_leaf list =
  tl (chain thy p) |> maps (fn (owner, Us) =>
    map2 (fn {name, acc, ...} => fn U => {name = name, typ = U, acc = acc, owner = owner})
      (#leaves (the_layer thy owner)) Us);

fun leaf_count thy name = length (flat_leaves thy (map TFree (#args (the_entry thy name)), name));

(*the concepts whose extension types make up T, the base first*)
fun type_layers thy T =
  let
    fun walk prev (Type (tyco, Ts as _ :: _)) =
          (case Symtab.lookup (#owners (Data.get thy)) tyco of
            SOME name =>
              let val up = Option.map (#owner o the_entry thy o #2) (#parent (the_entry thy name))
              in if up = prev then name :: walk (SOME name) (List.last Ts) else [] end
          | NONE => [])
      | walk _ _ = [];
  in walk NONE T end;

(*T as an instance of the scheme type of a concept: the type arguments and the more type*)
fun match_scheme thy T name =
  let
    val idx = Term.maxidx_of_typ T + 1;
    val varifyT = Term.map_type_tfree (fn (a, S) => TVar ((a, idx), S));
    val {args, scheme, more, ...} = the_entry thy name;
  in
    let
      val tyenv = Type.raw_match (varifyT scheme, T) Vartab.empty;
      val inst = Envir.norm_type tyenv o varifyT;
    in SOME (name, map (inst o TFree) args, inst (range_type (fastype_of more))) end
    handle Type.TYPE_MATCH => NONE
  end;

(*the deepest concept owning a layer of T of whose scheme type T is an instance: its type
  arguments and the more type*)
fun dest_scheme_type thy T = get_first (match_scheme thy T) (rev (type_layers thy T));

fun parent_of_type thy T = Option.map (fn (name, Ts, _) => (Ts, name)) (dest_scheme_type thy T);


(* balanced layout of a layer *)

val layerT = Balanced_Tree.make HOLogic.mk_prodT;
val mk_layer = Balanced_Tree.make HOLogic.mk_prod;

(*the components of a balanced tree of pairs with m leaves, as built by Balanced_Tree.make*)
fun projs 1 t = [t]
  | projs m t =
      let val k = m div 2
      in projs k (HOLogic.mk_fst t) @ projs (m - k) (HOLogic.mk_snd t) end;

(*split an equation between two layers into one equation per component*)
fun split_tac _ 1 _ = all_tac
  | split_tac ctxt m i =
      let val k = m div 2 in
        resolve_tac ctxt @{thms prod_eqI} i THEN
        split_tac ctxt (m - k) (i + 1) THEN split_tac ctxt k i
      end;

(*the canonical term over the layers abss, each with its leaves, innermost more last*)
fun whole_of thy abss leavess more =
  fold_rev (fn (a, ts) => fn t => app thy a (mk_layer (ts @ [t]))) (abss ~~ leavess) more;

(*a value of a concept: the base's leaf, the other leaves (flat_leaves order), and more*)
fun mk_value thy p base ts more =
  let
    val layers = chain thy p;
    val abss = map (#abs o the_layer thy o #1) layers;
    val leavess = [base] :: unflat (map #2 (tl layers)) ts;
  in whole_of thy abss leavess more end;


(* printing *)

(*the concepts that give their names to types, by the concept owning the last layer of their
  type: all but those whose type is that of their major parent*)
structure Printed = Theory_Data
(
  type T = string list Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge_list (op =);
);

(*the scheme types of two concepts are the same up to the names of their type variables*)
fun same_pattern thy name name' =
  let
    fun pattern idx c =
      Term.map_type_tfree (fn (a, S) => TVar ((a, idx), S)) (#scheme (the_entry thy c));
    fun matches (c, c') = can (Type.raw_match (pattern 0 c, pattern 1 c')) Vartab.empty;
  in matches (name, name') andalso matches (name', name) end;

fun register_printed name thy =
  let val {owner, parent, ...} = the_entry thy name in
    if owner = name orelse not (same_pattern thy name (#2 (the parent)))
    then Printed.map (Symtab.cons_list (owner, name)) thy else thy
  end;

(*the concept whose scheme type T is printed as, with the type arguments and the more type: the
  types that its type variables stand for are smallest in sum, then the first by name.
  Concepts with the same scheme type are passed over: none is an ancestor of another, as a
  concept with the type of its major parent is not listed*)
fun printed_as thy T =
  let
    fun cost (_, Ts, more) = fold (Integer.add o Term.size_of_typ) (more :: Ts) 0;
    val matches =
      maps (Symtab.lookup_list (Printed.get thy)) (type_layers thy T)
      |> map_filter (match_scheme thy T)
      |> sort (prod_ord int_ord string_ord o apply2 (fn m => (cost m, #1 m)));
    fun choose [] = NONE
      | choose ((m as (c, _, _)) :: ms) =
          if exists (same_pattern thy c o #1) ms
          then choose (filter_out (same_pattern thy c o #1) ms) else SOME m;
  in choose matches end;

(*print a concept type as C_scheme*)
fun type_tr' base_tyco =
  let val c = Lexicon.mark_type base_tyco in
    (c, fn ctxt => fn ts =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val T = Syntax_Phases.decode_typ (list_comb (Syntax.const c, ts));
      in
        (case printed_as thy T of
          SOME (name, Ts, more) =>
            Syntax_Phases.term_of_typ ctxt (Type (name ^ "_scheme", Ts @ [more]))
        | NONE => raise Match)
      end)
  end;

fun pretty_parent thy (Ts, name) = Syntax.string_of_typ_global thy (Type (name, Ts));

val implode_path = space_implode ".";

(*the noun for the number of xs*)
fun plural [_] noun = noun
  | plural _ noun = noun ^ "s";


(** sealed definitions **)

(*a binding that no input can reach: a fresh scope that no naming has entered*)
fun hidden b = Binding.restricted (SOME (true, Binding.new_scope ())) (Binding.concealed b);

(*the sealed definition of the constant declared with binding x: an extension segment after
  x's qualifiers, so that it is no user name and no other sealed name*)
fun sealed_def x =
  hidden
    (Binding.qualify_name true (Binding.map_name (K "extension") x) (Binding.name_of x ^ "_def"));

(*the constant x :: T and its sealed definition x == rhs, both under the current naming*)
fun define_sealed (x, T) rhs =
  Sign.declare_const_global ((x, T), NoSyn)
  #-> (fn c => Global_Theory.add_def (sealed_def x, Logic.mk_equals (c, rhs)) #>> pair c);

fun meta th = th RS @{thm eq_reflection};


(** paths in a node **)

(*a child of the node of a concept: a field (index into its leaves), or a view (its stored
  constant, its parent at the node's types, the slots of the parent's leaves)*)
datatype child =
  Field_Child of int
| View_Child of {const: term, parent: parent, more: typ, slots: slot list};

(*the fields and views of the node of p by name, each with the constant and the concept
  declaring it*)
fun children thy p =
  let
    val fields =
      map_index I (flat_leaves thy p)
      |> map_filter (fn (i, {name, owner, ...}) =>
          Option.map (fn c => (Long_Name.base_name c, (Field_Child i, (c, owner)))) name);
    val views =
      major_chain thy p |> maps (fn p' as (_, d) =>
        #views (the_entry thy d)
        |> map (fn {name, qualifier, const, parent = (Vs, r), more, slots, ...} =>
          (qualifier,
            (View_Child {const = const, parent = (map (subst_args thy p') Vs, r),
                more = subst_args thy p' more, slots = slots},
              (name, d)))));
  in fields @ views end;

(*the major parent of the node of p at its types, unless it is the base*)
fun super_of thy p =
  (case #parent (the_entry thy (#2 p)) of
    SOME (Us, q) => if q = base_name thy then NONE else SOME (map (subst_args thy p) Us, q)
  | NONE => NONE);

(*the first view of the node of p holding its anonymous leaf k: the view's qualifier, constant
  and parent, and the leaf's index in the parent*)
fun holder thy p k =
  (case get_first (fn (x, (View_Child {const, parent, slots, ...}, _)) =>
        (case find_index (fn s => s = Leaf k) slots of
          ~1 => NONE
        | r => SOME (x, const, parent, r))
      | _ => NONE) (children thy p) of
    SOME h => h
  | NONE => raise Fail "holder: an anonymous leaf held by no view");

(*the more slot of a node counts as the leaf after its leaves*)
fun is_more thy p k = k = length (flat_leaves thy p);

(*leaf k of a structure t of concept p as users see it: the selector applied to t for a named
  leaf and for more; for an anonymous leaf, the read through its holder*)
fun read_leaf thy p k t =
  if is_more thy p k then app thy (#more (the_entry thy (#2 p))) t
  else
    (case nth (flat_leaves thy p) k of
      {name = SOME _, acc, ...} => app thy acc t
    | _ =>
        let val (_, const, parent, r) = holder thy p k
        in read_leaf thy parent r (app thy const t) end);

(*the path naming leaf k of concept p*)
fun leaf_path thy p k =
  if is_more thy p k then ["more"]
  else
    (case nth (flat_leaves thy p) k of
      {name = SOME c, ...} => [Long_Name.base_name c]
    | _ => let val (x, _, parent, r) = holder thy p k in x :: leaf_path thy parent r end);

(*a node: its concept, the type of its more slot where that is fixed, its slots, the constants
  of the views on the path to it*)
datatype target = Slot of slot | Node of parent * typ option * slot list * string list;

(*the path walked so far, the node, the missing name and its position*)
exception NO_FIELD of string list * parent * string * Position.T;

(*resolve a path in the node of concept p with the given slots: those of its leaves, then that
  of its more unless the more is (); views: the constants of the views passed, the last first*)
fun resolve _ p more slots views _ [] = Node (p, more, slots, rev views)
  | resolve thy p _ slots views walked ((seg, pos) :: segs) =
      (case (AList.lookup (op =) (children thy p) seg, seg) of
        (SOME (Field_Child i, _), _) =>
          if null segs then Slot (nth slots i)
          else raise NO_FIELD (walked, p, implode_path (seg :: map #1 segs), pos)
      | (SOME (View_Child {parent = p', more, slots = vslots, ...}, (c, _)), _) =>
          resolve thy p' (SOME more) (map (fn Leaf i => nth slots i | g => g) vslots)
            (c :: views) (walked @ [seg]) segs
      | (NONE, "super") =>
          (case super_of thy p of
            SOME p' =>
              resolve thy p' NONE (take (length (flat_leaves thy p')) slots) views
                (walked @ [seg]) segs
          | NONE => raise NO_FIELD (walked, p, seg, pos))
      | (NONE, "more") =>
          if null segs andalso length slots > length (flat_leaves thy p)
          then Slot (List.last slots) else raise NO_FIELD (walked, p, seg, pos)
      | (NONE, _) => raise NO_FIELD (walked, p, seg, pos));

(*the second line of the messages about a missing field of the node of p*)
fun fields_line thy p =
  let
    val fields = map #1 (children thy p);
    val super =
      (case super_of thy p of
        SOME (_, q) => "; super stands for its " ^ Long_Name.base_name q ^ " part"
      | NONE => "");
  in
    (case fields of
      [] => "It has no fields"
    | [x] => "Its field is " ^ x
    | _ => "Its fields are " ^ commas fields) ^ super
  end;

(*the parent named by the path prefix @ walked of concept cname, or cname itself when that path
  is empty, has no field seg*)
fun no_field_error thy cname prefix (walked, p, seg, pos) =
  let
    val path = prefix @ walked;
    val head =
      if null path then "The concept " ^ cname
      else
        "The parent " ^ implode_path path ^ ": " ^ quote (pretty_parent thy p) ^ " of concept " ^
          cname;
  in error (head ^ " has no field named " ^ seg ^ Position.here pos ^ "\n" ^ fields_line thy p) end;


(* where clauses *)

(*what a where clause gives: one leaf of the parent, or a node as a whole, each of whose leaves
  (leaf of the parent, leaf of the node) is read from the value; with the constants of the views
  on the path to the node*)
datatype given =
  Given_Leaf of int | Given_Node of parent * typ option * (int * int) list * string list;

(*the leaves of the parent that a where clause gives, each with its path below the clause's*)
fun given_leaves _ (Given_Leaf j) = [(j, [])]
  | given_leaves thy (Given_Node (p', _, jks, _)) =
      map (fn (j, k) => (j, leaf_path thy p' k)) jks;

(*no leaf of p given twice; owner names p as the user named it*)
fun check_twice thy p owner entries =
  let
    (*a leaf with the clause giving it: its index, its path, the leaf's path below it*)
    val assigned =
      flat (map_index (fn (i, (path, _, g)) =>
        map (fn (j, sub) => (j, (i, path, sub))) (given_leaves thy g)) entries);
  in
    assigned |> List.app (fn (j, _) =>
      (case filter (fn (j', _) => j' = j) assigned of
        (_, (i0, path0, sub0)) :: (_, (i2, path2, sub2)) :: _ =>
          let
            (*two leaves of one clause are told apart by their paths below it*)
            fun shown path sub = implode_path (map #1 path @ (if i0 = i2 then sub else []));
            val p0 = shown path0 sub0 and p2 = shown path2 sub2;
          in
            error ("The field " ^ implode_path (leaf_path thy p j) ^ " of " ^ owner ^
              " is specified twice" ^
              (if p0 = p2 then "" else ": by " ^ quote p0 ^ " and by " ^ quote p2) ^
              Position.here (#2 (List.last path2)))
          end
      | _ => ()))
  end;

(*the leaves of a node of concept p whose more slot has the type more: those of p, then the
  more slot unless it is ()*)
fun node_leaves thy (p as (_, name), more) : flat_leaf list =
  flat_leaves thy p @
    (if more = HOLogic.unitT then []
     else
      [{name = NONE, typ = more, acc = #more (the_entry thy name),
        owner = #owner (the_entry thy name)}]);

(*resolve the where clauses in the node of p with the more slot of type more; owner names the
  node as the user named it; a clause may not reach a leaf that the parent's where clause
  already gave, directly or through a node*)
fun resolve_entries thy (p, more) no_field owner where_ =
  let
    val ident = map Leaf (0 upto length (node_leaves thy (p, more)) - 1);
    fun already_given path pos (d, t) =
      error ("The field " ^ implode_path path ^ Position.here pos ^ " of " ^ owner ^
        " is already specified by " ^ Long_Name.base_name d ^ " itself as " ^
        quote (Syntax.string_of_term_global thy t) ^ "; it cannot be specified again");
    fun entry (path, rhs) =
      let
        val pos = #2 (List.last path);
        (*the leaf of p in a slot; sub: its path below the clause's path*)
        fun leaf _ (Leaf j) = j
          | leaf sub (Given g) = already_given (map #1 path @ sub ()) pos g;
      in
        (case resolve thy p (SOME more) ident [] [] path handle NO_FIELD e => no_field e of
          Slot s => (path, rhs, Given_Leaf (leaf (K []) s))
        | Node (p', more', slots, views) =>
            (path, rhs,
              Given_Node (p', more',
                map_index (fn (k, s) => (leaf (fn () => leaf_path thy p' k) s, k)) slots, views)))
      end;
    val entries = map entry where_;
    val _ = check_twice thy p owner entries;
  in entries end;

(*read the right-hand side of a where clause in the node of p with the more slot of type more,
  against the type of what it gives: a leaf; a node, with any extension when the type of its
  more slot is not fixed (super)*)
fun read_given thy ctxt (p, more) owner (path, rhs, given) =
  let
    val pos = #2 (List.last path);
    val path_s = implode_path (map #1 path);
    val (T, show_T) =
      (case given of
        Given_Leaf j => let val {typ, ...} = nth (node_leaves thy (p, more)) j in (typ, typ) end
      | Given_Node (p' as (Ts, _), NONE, _, _) =>
          (scheme_type thy p' dummyT,
            scheme_type thy p' (TFree (more_var (map #1 (fold Term.add_tfreesT Ts [])))))
      | Given_Node (p', SOME more', _, _) => let val U = scheme_type thy p' more' in (U, U) end);
  in
    (Syntax.parse_term ctxt rhs |> Type.constraint T |> Syntax.check_term ctxt)
      handle ERROR msg =>
        let
          val u = Syntax.read_term ctxt rhs handle ERROR _ => error msg;
          val shown = quote (Syntax.string_of_typ ctxt show_T);
          val value =
            quote (Syntax.string_of_term ctxt u) ^ " has type " ^
              quote (Syntax.string_of_typ ctxt (fastype_of u));
        in
          (case (given, #1 (List.last path)) of
            (Given_Node (p', _, _, _), "super") =>
              error (path_s ^ Position.here pos ^ " of " ^ owner ^ " stands for its " ^
                Long_Name.base_name (#2 p') ^ " part, of type " ^ shown ^
                ", but the given value " ^ value)
          | _ =>
              error ("The field " ^ path_s ^ Position.here pos ^ " of " ^ owner ^
                " expects type " ^ shown ^ ", but the given value " ^ value))
        end
  end;

(*the right-hand side of the where clause naming field (quoted, with its position) uses x, which
  nothing defines*)
fun undefined_constant field x =
  error ("The assignment of the field " ^ field ^ " uses undefined constant " ^ quote x);

(*the types in the right-hand side t of the where clause naming field are determined: its type
  variables are among those of T, the type of the constant being defined*)
fun check_determined ctxt T field t =
  (case Undetermined_Types.to_annotate (Term.add_tfreesT T []) t of
    [] => ()
  | terms =>
      error ("The assignment of the field " ^ field ^ " " ^ Undetermined_Types.message ctxt terms));

(*the leaves that a where clause gives, with their values*)
fun given_values _ (Given_Leaf j) t = [(j, t)]
  | given_values thy (Given_Node (p', _, jks, _)) t =
      map (fn (j, k) => (j, read_leaf thy p' k t)) jks;


(** the selector Simpset **)

(*a congruence rule f xs == f ys under which every argument is rewritten; one with the same term
  at an argument of both sides (the branches of if and case) leaves that argument as it is*)
fun rewrites_all_args cong =
  let val (lhs, rhs) = Logic.dest_equals (Thm.concl_of cong)
  in not (ListPair.exists (op aconv) (#2 (strip_comb lhs), #2 (strip_comb rhs))) end;

(*the simpset for rewriting inside the package: the simpset of the theory loading this file
  without its rewrite rules, simprocs and loopers, with those of its congruence rules again
  under which every argument is rewritten; the selector simprocs are added to it.  Under these
  congruence rules the simplifier assumes one side while it rewrites the other, and what it
  assumes becomes rewrite rules there, as in simp*)
structure Selector_Simpset = Generic_Data
(
  type T = simpset;
  val empty =
    let
      val ctxt = Context.the_local_context ();
      val congs =
        filter rewrites_all_args (map #2 (Simplifier.dest_congs (Simplifier.simpset_of ctxt)));
    in
      Simplifier.clear_simpset ctxt |> fold Simplifier.add_eqcong congs |> Simplifier.simpset_of
    end;
  val merge = Simplifier.merge_ss;
);

(*change the selector Simpset: f gets a context having it as simpset*)
fun map_selector_simpset f context =
  Selector_Simpset.map (Simplifier.simpset_map (Context.proof_of context) f) context;

(*the only way to use the selector Simpset: the context having it as simpset, with the premises
  that a surrounding simplification has assumed (put_simpset alone drops them)*)
fun put_selector_simpset ctxt =
  ctxt
  |> Simplifier.put_simpset (Selector_Simpset.get (Context.Proof ctxt))
  |> Simplifier.add_prems (Simplifier.prems_of ctxt);


(** the selector simproc **)

(*what a stored instance applied to args makes of a term over its parameters, m instantiating
  what is stored*)
fun instance_subst m ({params, ...}: instance_entry) args = subst_free (map m params ~~ args) o m;

(*the same at the actual type T of the constant of the instance*)
fun instance_term thy (inst as {const, ...}: instance_entry) T =
  instance_subst (matcher thy const T) inst;

(*an instance at the actual type T of its constant, applied to args: values, more*)
fun instance_at thy (inst as {values, more, ...}: instance_entry) T args =
  let val subst = instance_term thy inst T args in (map subst values, subst more) end;

(*the structure t from which a structure of concept name has what lies beyond the layers of
  its type: its more is stored as L.more t, L owning the last of these layers*)
fun beyond thy name more =
  (case more of
    Const (mc, _) $ t => if mc = dest_Const_name (#more (the_entry thy name)) then SOME t else NONE
  | _ => NONE);

fun the_view thy d c = the (find_first (fn {name, ...} => name = c) (#views (the_entry thy d)));

(*what a constant is to the simproc; nothing is instantiated*)
datatype head = Instance_Head of instance_entry | View_Head of view_entry | Truncate_Head of string;

fun head_of thy c =
  (case get_instance_entry thy c of
    SOME inst => SOME (Instance_Head inst)
  | NONE =>
      (case get_kind thy c of
        SOME (View_Const d) => SOME (View_Head (the_view thy d c))
      | SOME (Truncate d) => SOME (Truncate_Head d)
      | _ => NONE));

(*what a term is by its head, with the type of the constant and the arguments: an instance
  applied to all its parameters; a view or a truncation applied to one structure*)
fun dest_head thy w =
  (case strip_comb w of
    (Const (c, T), args) =>
      (case (head_of thy c, args) of
        (SOME (head as Instance_Head {params, ...}), _) =>
          if length args = length params then SOME (head, T, args) else NONE
      | (SOME head, [_]) => SOME (head, T, args)
      | _ => NONE)
  | _ => NONE);

(*P and u of P.truncate u*)
fun dest_truncation thy w =
  (case dest_head thy w of SOME (Truncate_Head P, _, [u]) => SOME (P, u) | _ => NONE);

(*leaf j of a structure w as a term: the selector applied to w for a named leaf; for an
  anonymous one its value from w's head, else the read through its view*)
fun leaf_term thy j w =
  (case parent_of_type thy (fastype_of w) of
    NONE => NONE
  | SOME p =>
      (case nth (flat_leaves thy p) j of
        {name = SOME _, ...} => SOME (read_leaf thy p j w)
      | _ => (case leaf_value thy j w of NONE => SOME (read_leaf thy p j w) | some => some)))

(*the value of leaf j of a structure w, one step from the definition of its head; a leaf beyond
  the layers of the head's type is that of the structure whose more the head stores*)
and leaf_value thy j w =
  let fun stored name more = Option.mapPartial (leaf_term thy j) (beyond thy name more) in
    (case dest_head thy w of
      SOME (Instance_Head (inst as {concept = (_, name), ...}), T, args) =>
        let val (values, more) = instance_at thy inst T args
        in if j < length values then SOME (nth values j) else stored name more end
    | SOME (View_Head (view as {parent = (_, r), ...}), T, [w']) =>
        if j < leaf_count thy r then view_slot thy view T w' j
        else Option.mapPartial (stored r) (view_more thy view T w')
    | SOME (Truncate_Head d, _, [r]) => if j < leaf_count thy d then leaf_term thy j r else NONE
    | _ => NONE)
  end

(*the value of slot j of a view at the type T of its constant, applied to w'*)
and view_slot thy ({const, slots, S, values, ...}: view_entry) T w' j =
  (case nth slots j of
    Leaf i => leaf_term thy i w'
  | Given _ =>
      let val m = matcher thy const T
      in SOME (subst_free [(m S, w')] (m (nth values j))) end)

(*the value of the more slot of a view with one, unless it is known only as the more of the
  view itself*)
and view_more thy (view as {const, slots, parent = (_, r), ...}: view_entry) T w' =
  let val n = leaf_count thy r in
    if length slots = n then NONE
    else
      view_slot thy view T w' n
      |> Option.mapPartial (fn m =>
        if beyond thy r m = SOME (matcher thy const T const $ w') then NONE else SOME m)
  end;

(*the value of the more of the layer of concept d of a structure w*)
fun more_value thy d w =
  let
    (*the more of the last layer L of the head's type is m: the more of L itself, that of a
      layer beyond*)
    fun stored name m =
      let val L = #owner (the_entry thy name) in
        if d = L then SOME m
        else if member (op =) (layers_from thy L) d then NONE
        else Option.map (app thy (#more (the_entry thy d))) (beyond thy name m)
      end;
  in
    (case dest_head thy w of
      SOME (Instance_Head (inst as {concept = (_, name), ...}), T, args) =>
        stored name (#2 (instance_at thy inst T args))
    | SOME (View_Head (view as {slots, parent = (_, r), ...}), T, [w']) =>
        if length slots = leaf_count thy r
        then if d = #owner (the_entry thy r) then SOME HOLogic.unit else NONE
        else Option.mapPartial (stored r) (view_more thy view T w')
    | SOME (Truncate_Head e, _, _) => if d = e then SOME HOLogic.unit else NONE
    | _ => NONE)
  end;

fun add_tycos (Type (c, Ts)) = insert (op =) c #> fold add_tycos Ts
  | add_tycos _ = I;

(*the fixed rules that unfold the structures in ts down to their leaves*)
fun unfold_rules thy ts =
  let
    val owners = Symtab.lookup (#owners (Data.get thy));
    val layers =
      fold (Term.fold_types add_tycos) ts [] |> map_filter owners |> map (the_layer thy);
    fun def_of c =
      (case head_of thy c of
        SOME (Instance_Head {def, ...}) => [def]
      | SOME (View_Head {def, ...}) => [def]
      | SOME (Truncate_Head d) => [#truncate_def (the_layer thy d)]
      | NONE => []);
  in
    maps #defs layers @ map (meta o #abs_inverse) layers @
    maps def_of (fold Term.add_const_names ts []) @ map meta @{thms fst_conv snd_conv}
  end;

(*a term unfolded down to its leaves: the fixed rules of the constants in it and of those that
  the unfolding brings up; defs: the definitions of constants that the theory does not know yet*)
fun unfold_conv ctxt defs ct =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun unfold th =
      let
        val ct' = Thm.rhs_of th;
        val rules = defs @ unfold_rules thy [Thm.term_of ct'];
        val th' = Raw_Simplifier.rewrite_wrt ctxt false rules ct';
      in if Thm.is_reflexive th' then th else unfold (Thm.transitive th th') end;
    val th = unfold (Thm.reflexive ct);
  in Thm.transitive th (Thm.eta_conversion (Thm.rhs_of th)) end;

(*lhs == rhs: both sides converted to the same term; the variables stay as they are*)
fun prove_by_conv conv ctxt lhs rhs =
  let val l = conv (Thm.cterm_of ctxt lhs) and r = conv (Thm.cterm_of ctxt rhs) in
    if Thm.rhs_of l aconvc Thm.rhs_of r then SOME (Thm.transitive l (Thm.symmetric r)) else NONE
  end;

(*both sides unfolded to the same normal form, compared modulo eta*)
fun prove_select_with ctxt defs = prove_by_conv (unfold_conv ctxt defs) ctxt;

fun prove_select ctxt = prove_select_with ctxt [];

(*lhs = rhs as a theorem of the theory, the variables xs and all types schematic*)
fun prove_unfold thy defs xs lhs rhs =
  Goal.prove_sorry_global thy xs [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
    (fn {context = ctxt, ...} =>
      (case prove_select_with ctxt defs lhs rhs of
        SOME th => resolve_tac ctxt [th RS @{thm meta_eq_to_obj_eq}] 1
      | NONE => no_tac));


(** the cache of the equations **)

(*The equations that the simprocs prove, by their left sides: constants of this package applied
  to schematic variables.  An equation is kept until a garbage collection finds it unused; the
  count is of the equations stored since the dead entries were last removed.*)
val cache =
  Synchronized.var "Concept_Type.cache"
    (0, Termtab.empty: thm Unsynchronized.weak_ref Termtab.table);

(*the finished ancestor theory that has every constant and type constructor of t and in which
  the constants of t have well-sorted types, if any: what is proved there serves all theories
  that import it*)
fun home thy t =
  let
    val names =
      map (Name_Space.theory_name {long = true} (Sign.const_space thy))
        (Term.add_const_names t []) @
      map (Name_Space.theory_name {long = true} (Sign.type_space thy))
        (Term.fold_types add_tycos t [])
      |> distinct (op =);
    val thys = map (try (Context.get_theory {long = true} thy)) names;
    (*a class or an arity of the types of t may be younger than the theory*)
    fun well_sorted thy' =
      Term.fold_aterms (fn Const (c, T) => (fn ok =>
          ok andalso Sign.typ_instance thy' (T, Sign.the_const_type thy' c))
        | _ => I) t true;
  in
    if null thys orelse exists is_none thys then NONE
    else
      let val thys' = map the thys in
        find_first (fn thy' => forall (fn thy'' => Context.subthy (thy'', thy')) thys') thys'
        |> Option.mapPartial (Option.filter well_sorted)
      end
  end;

(*the meta equation whose left side is key: the one stored, when the theory has the theory of
  that; else proved, in the home of key or in the theory, apart from what the context assumes,
  and stored unless the one stored serves the theories that the new one serves*)
fun cached ctxt key prove =
  let
    val thy = Proof_Context.theory_of ctxt;
    val peek = Option.mapPartial Unsynchronized.weak_peek oo Termtab.lookup;
    fun serves th th' = Context.subthy_id (Thm.theory_id th, Thm.theory_id th');
    fun store th (n, tab) =
      let
        val tab' =
          if (case peek tab key of SOME th' => serves th' th | NONE => false) then tab
          else Termtab.update (key, Unsynchronized.weak_ref th) tab;
        fun live (entry as (_, r)) = Unsynchronized.weak_active r ? Termtab.update entry;
      in if n < 255 then (n + 1, tab') else (0, Termtab.fold live tab' Termtab.empty) end;
    fun proved () =
      let
        val ctxts = map Proof_Context.init_global (the_list (home thy key) @ [thy]);
      in
        get_first prove ctxts |> Option.map (fn th =>
          (Synchronized.change cache (store (Thm.trim_context th)); Thm.transfer thy th))
      end;
  in
    (case peek (#2 (Synchronized.value cache)) key of
      SOME th =>
        if Context.subthy_id (Thm.theory_id th, Context.theory_id thy)
        then SOME (Thm.transfer thy th) else proved ()
    | NONE => proved ())
  end;

(*a meta equation, with premises or without, instantiated so that its left side is ct*)
fun at_cterm ct th =
  let
    val th' = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) th;
    val lhs = Thm.dest_equals_lhs (Thm.cconcl_of th');
  in Thm.instantiate (Thm.match (lhs, ct)) th' end;

(*a structure with its instance, view and truncate constants kept and every other term in it
  replaced by a schematic variable, equal terms by one variable*)
fun skeleton thy w (seen: (term * term) list) =
  let
    fun variable () =
      (case AList.lookup (op aconv) seen w of
        SOME x => (x, seen)
      | NONE =>
          let val x = Var (("x", length seen), fastype_of w) in (x, (w, x) :: seen) end);
  in
    (case dest_head thy w of
      SOME (_, _, args) => fold_map (skeleton thy) args seen |>> curry list_comb (Term.head_of w)
    | NONE => variable ())
  end;

(*the value of a selector on a structure as it is stored, ct being the selector applied to the
  structure: the equation is that of the skeleton of the structure*)
fun stored_value ctxt value ct =
  let
    val (f, w) = Term.dest_comb (Thm.term_of ct);
    val (w', _) = skeleton (Proof_Context.theory_of ctxt) w [];
    val key = f $ w';
    fun prove ctxt' =
      value (Proof_Context.theory_of ctxt') w' |> Option.mapPartial (fn rhs =>
        if rhs aconv key then NONE else prove_select ctxt' key rhs);
  in
    if is_Var w' then NONE
    else Option.map (at_cterm ct) (cached ctxt key prove)
  end;

(*the case constant of a datatype with one constructor: the constructor, the case theorem*)
fun single_case ctxt c =
  (case Case_Translation.lookup_by_case ctxt c of
    SOME (_, [ctr]) =>
      (case Ctr_Sugar.ctr_sugar_of ctxt (dest_Type_name (body_type (fastype_of ctr))) of
        SOME {case_thms = [th], ...} => SOME (ctr, th)
      | _ => NONE)
  | _ => NONE);

(*a value that begins with a pattern, as in %(a, b). t: under abstractions, such a case awaits
  its argument*)
fun begins_with_pattern ctxt v =
  let fun body (Abs (_, _, b)) = body b | body t = t in
    (case body (Envir.eta_contract v) of
      Const (c, _) $ _ => is_some (single_case ctxt c)
    | _ => false)
  end;

(*beta, and such a case at an explicit value of its datatype, at the head of ct for as long as
  the head is an abstraction or such a case; none when a case meets another argument or none*)
fun reduce ctxt ct =
  let
    fun explicit ctr u =
      (case strip_comb u of
        (Const (c, _), xs) =>
          c = dest_Const_name ctr andalso length xs = length (binder_types (fastype_of ctr))
      | _ => false);
    fun loop th =
      let
        val (h, us) = strip_comb (Thm.term_of (Thm.rhs_of th));
        val k = length us;
        (*the head with its first arguments, the last k' left aside*)
        fun step k' cv = loop (Thm.transitive th (funpow k' Conv.fun_conv cv (Thm.rhs_of th)));
      in
        (case h of
          Abs _ => if k = 0 then SOME th else step (k - 1) (Thm.beta_conversion false)
        | Const (c, _) =>
            (case single_case ctxt c of
              SOME (ctr, case_thm) =>
                if k >= 2 andalso explicit ctr (nth us 1)
                then step (k - 2) (Conv.rewr_conv (meta case_thm)) else NONE
            | NONE => SOME th)
        | _ => SOME th)
      end;
  in loop (Thm.reflexive ct) end;

(*the value of a selector on a structure, ct being the selector applied to it; none for a value
  that begins with a pattern*)
fun select ctxt value ct =
  stored_value ctxt value ct |> Option.mapPartial (fn th =>
    if begins_with_pattern ctxt (Thm.term_of (Thm.rhs_of th)) then NONE else SOME th);

(*a selector on a structure and further arguments, where the value on the structure begins with
  a pattern: that value at the arguments, when they are explicit as far as the pattern goes*)
fun select_applied ctxt value ct =
  let
    val (f, w :: args) = Drule.strip_comb ct;
    val applied = fold (fn a => fn th => Thm.combination th (Thm.reflexive a)) args;
  in
    stored_value ctxt value (Thm.apply f w) |> Option.mapPartial (fn th =>
      if begins_with_pattern ctxt (Thm.term_of (Thm.rhs_of th)) then
        let val th' = applied th
        in Option.map (Thm.transitive th') (reduce ctxt (Thm.rhs_of th')) end
      else NONE)
  end;


(** truncate **)

(* what is stored *)

(*what truncate does at the layer L, the next layer toward the base being L':
  concept: concept (L.truncate ?r) = concept ?r;
  ident: L.truncate ?r = ?r, the more of ?r being ();
  up: L.truncate ?u = L.truncate ?v ==> L'.truncate ?u = L'.truncate ?v, and the same between
    the concept.more of these four terms*)
type laws = {concept: thm, ident: thm, up: (thm * thm) option};

(*with the laws of every layer, that of the base:
  concept ?x ==> concept ?y ==> concept.more ?x = concept.more ?y ==> ?x = ?y*)
structure Laws = Theory_Data
(
  type T = thm option * laws Symtab.table;
  val empty = (NONE, Symtab.empty);
  fun merge ((base, laws), (base', laws')) =
    (if is_some base then base else base', Symtab.merge (K true) (laws, laws'));
);

fun map_laws_thms f ({concept, ident, up}: laws) : laws =
  {concept = f concept, ident = f ident, up = Option.map (apply2 f) up};

fun the_laws thy layer =
  map_laws_thms (Thm.transfer thy) (the (Symtab.lookup (#2 (Laws.get thy)) layer));
fun put_laws layer laws =
  Laws.map (apsnd (Symtab.update (layer, map_laws_thms Thm.trim_context laws)));

fun base_equality thy = Thm.transfer thy (the (#1 (Laws.get thy)));

fun mk_truncate thy layer = app thy (#truncate (the_layer thy layer));
fun mk_concept thy t = Const (base_name thy, fastype_of t --> HOLogic.boolT) $ t;
fun mk_base_more thy = app thy (#more (the_entry thy (base_name thy)));

val mk_prop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;

(*a u = a v ==> b u = b v for the variables u and v, where eq is f (a ?r) = b ?r; xs: the other
  variables of the statement*)
fun lift thy xs (u, v) a b f eq =
  Goal.prove_sorry_global thy (map (#1 o dest_Free) [u, v] @ xs) [mk_prop_eq (a u, a v)]
    (mk_prop_eq (b u, b v))
    (fn {context = ctxt, prems} =>
      let
        val ct = Thm.cterm_of ctxt;
        fun at x = Drule.infer_instantiate ctxt [(("r", 0), ct x)] eq;
        val cong = Drule.infer_instantiate ctxt [(("f", 0), ct f)] @{thm arg_cong} OF prems;
        val sym = @{thm sym} and trans = @{thm trans};
      in resolve_tac ctxt [trans OF [at u RS sym, trans OF [cong, at v]]] 1 end);

(*the laws of the layer of concept name, which is registered*)
fun add_laws name thy =
  let
    val {args, layer, more, ...} = the_entry thy name;
    val {truncate_def, surjective, ...} = the layer;
    val p = (map TFree args, name);
    val [m, n] =
      Name.variant_list (map #1 args) ["'m", "'n"]
      |> map (fn a => TFree (a, \<^sort>\<open>type\<close>));
    val r = Free ("r", scheme_type thy p m);
    val truncate = mk_truncate thy name;
    val concept = prove_unfold thy [] ["r"] (mk_concept thy (truncate r)) (mk_concept thy r);
    val r0 = Free ("r", unit_type thy p);
    val ident =
      Goal.prove_sorry_global thy ["r"] [] (mk_prop_eq (truncate r0, r0))
        (fn {context = ctxt, ...} =>
          let
            val unit =
              Thm.instantiate' [] [SOME (Thm.cterm_of ctxt (app thy more r0))] @{thm unit_eq};
          in
            rewrite_goals_tac ctxt [truncate_def] THEN
            resolve_tac ctxt @{thms trans} 1 THEN
            resolve_tac ctxt [surjective RS @{thm sym}] 2 THEN
            rewrite_goals_tac ctxt [meta unit] THEN
            resolve_tac ctxt @{thms refl} 1
          end);
    fun up below =
      let
        val truncate' = mk_truncate thy below;
        val base_more = mk_base_more thy;
        val u = Free ("u", scheme_type thy p m) and v = Free ("v", scheme_type thy p n);
        val x = Free ("x", unit_type thy p);
        val merged = prove_unfold thy [] ["r"] (truncate' (truncate r)) (truncate' r);
        (*the concept.more of L'.truncate from that of L.truncate: put under the base again*)
        val y = Free ("y", fastype_of (base_more x));
        val base_abs = #abs (the_layer thy (base_name thy));
        val rebuild =
          lambda y
            (base_more
              (truncate' (app thy base_abs (HOLogic.mk_prod (\<^Const>\<open>True\<close>, y)))));
        val split =
          prove_unfold thy [] ["r"] (betapply (rebuild, base_more (truncate r)))
            (base_more (truncate' r));
      in
        (lift thy [] (u, v) truncate truncate' (lambda x (truncate' x)) merged,
          lift thy [] (u, v) (base_more o truncate) (base_more o truncate') rebuild split)
      end;
  in
    thy |> put_laws name
      {concept = concept, ident = ident, up = Option.map up (layer_below thy name)}
  end;

(*the law of the base, from the equality of its layer*)
fun add_base_equality thy =
  let
    val base = base_name thy;
    val {equality, ...} = the_layer thy base;
    val T = scheme_type thy ([], base) (TFree (more_var []));
    val x = Free ("x", T) and y = Free ("y", T);
    val base_more = mk_base_more thy;
    val th =
      Goal.prove_sorry_global thy ["x", "y"]
        [HOLogic.mk_Trueprop (mk_concept thy x), HOLogic.mk_Trueprop (mk_concept thy y),
          mk_prop_eq (base_more x, base_more y)]
        (mk_prop_eq (x, y))
        (fn {context = ctxt, prems = [px, py, more_eq]} =>
            resolve_tac ctxt [equality] 1 THEN resolve_tac ctxt @{thms iffI} 1 THEN
            EVERY (map (fn th => resolve_tac ctxt [th] 1) [py, px, more_eq])
          | _ => no_tac);
  in Laws.map (apfst (K (SOME (Thm.trim_context th)))) thy end;


(* what follows from it *)

(*an equation L.truncate u = L.truncate v, or one between the concept.more of the two sides
  (which = #2), moved to the layer P, which is L or nearer to the base*)
fun at_layer which thy P L th =
  if L = P then th
  else
    at_layer which thy P (the (layer_below thy L)) (which (the (#up (the_laws thy L))) OF [th]);

(*P.truncate (Q.truncate ?r) = P.truncate ?r, the layer Q being P or farther from the base*)
fun truncate_merge thy P Q =
  let
    val {args, ...} = the_entry thy Q;
    val ctxt = Proof_Context.init_global thy;
    val r = Free ("r", scheme_type thy (map TFree args, Q) (TFree (more_var (map #1 args))));
    val twice =
      Drule.infer_instantiate ctxt [(("r", 0), Thm.cterm_of ctxt (mk_truncate thy Q r))]
        (#ident (the_laws thy Q));
  in Drule.export_without_context (at_layer #1 thy P Q twice) end;

(*concept ?x ==> concept ?y ==> L.truncate ?x = L.truncate ?y, from
  concept.more (L.truncate x) = concept.more (L.truncate y)*)
fun truncate_eq_of_fields thy L fields =
  let val truncated = #concept (the_laws thy L) RS @{thm iffD2}
  in base_equality thy OF [truncated, truncated, fields] end;

(*a theorem instantiated so that the subterm of its proposition that select gives becomes obj;
  the variables of obj are kept apart.  The matching is on terms: an obj that is ill-typed or
  does not fit fails with Pattern.MATCH*)
fun instantiate_at ctxt select obj th =
  let
    val thy = Proof_Context.theory_of ctxt;
    val th' = Thm.incr_indexes (Term.maxidx_of_term obj + 1) th;
    val (tyenv, tenv) =
      Pattern.match thy (select (Thm.prop_of th'), obj) (Vartab.empty, Vartab.empty);
    val instT =
      TVars.build (tyenv |> Vartab.fold (fn (xi, (S, T)) =>
        TVars.add ((xi, S), Thm.ctyp_of ctxt T)));
    val inst =
      Vars.build (tenv |> Vartab.fold (fn (xi, (T, u)) =>
        Vars.add ((xi, Envir.subst_type tyenv T), Thm.cterm_of ctxt u)));
  in Thm.instantiate (instT, inst) th' end;

val concl_of = HOLogic.dest_Trueprop o Logic.strip_imp_concl;
val lhs_of = #1 o HOLogic.dest_eq o concl_of;
val rhs_of = #2 o HOLogic.dest_eq o concl_of;
(*the two sides of an equation as one term*)
val sides_of = HOLogic.mk_prod o HOLogic.dest_eq o concl_of;
(*the structure t of ... ==> concept t, and of concept t ==> ...*)
val structure_of = #2 o dest_comb o concl_of;
val premise_structure_of = #2 o dest_comb o HOLogic.dest_Trueprop o hd o Logic.strip_imp_prems;

(*a term under an instantiation got by matching; a term instantiated before can be
  instantiated again*)
fun instantiated ((tyenv, tenv): Type.tyenv * Envir.tenv) =
  Envir.norm_term (Envir.Envir {maxidx = ~1, tenv = tenv, tyenv = tyenv});

(*the pattern has none of the variables that env instantiates*)
fun matches thy pair env =
  SOME (Pattern.match thy pair env) handle Pattern.MATCH => NONE | Pattern.Pattern => NONE;

(*instantiate_at will give a theorem: the same matching, on terms only*)
fun fits thy select obj th =
  let val prop = Logic.incr_indexes ([], Term.maxidx_of_term obj + 1) (Thm.prop_of th)
  in is_some (matches thy (select prop, obj) (Vartab.empty, Vartab.empty)) end;

(*for an instance or a view u applied to its arguments: its theorem concept (c ?xs) = H, and
  the hidden field of u, which is H at u*)
fun hidden_field thy u =
  let
    fun at th =
      let
        val (lhs, rhs) =
          HOLogic.dest_eq
            (concl_of (Logic.incr_indexes ([], Term.maxidx_of_term u + 1) (Thm.prop_of th)));
      in
        matches thy (#2 (dest_comb lhs), u) (Vartab.empty, Vartab.empty)
        |> Option.map (fn env => (th, instantiated env rhs))
      end;
  in
    (case dest_head thy u of
      SOME (Instance_Head {concept_eq, ...}, _, _) => at concept_eq
    | SOME (View_Head {concept_eq, ...}, _, _) => at concept_eq
    | _ => NONE)
  end;

(*concept u = H from that theorem, H as hidden_field gives it modulo beta*)
fun hidden_at ctxt u th = instantiate_at ctxt (#2 o dest_comb o lhs_of) u th;

(*concept t, when the hidden field of t is True: t an instance or a view, under truncations*)
fun concept_holds ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    (case dest_truncation thy t of
      SOME (d, u) =>
        concept_holds ctxt u
        |> Option.map (Thm.implies_elim
          (instantiate_at ctxt structure_of t (#concept (the_laws thy d) RS @{thm iffD2})))
    | NONE =>
        (case hidden_field thy t of
          SOME (th, \<^Const_>\<open>True\<close>) => SOME (hidden_at ctxt t th RS @{thm eqTrueE})
        | _ => NONE))
  end;

val ident_of = meta o #ident oo the_laws;

(*(A ==> B ==> C) ==> (A ==> B) ==> A ==> C*)
val follows_rule =
  let
    val [A, B, C] = map (fn x => Thm.global_cterm_of \<^theory> (Free (x, propT))) ["A", "B", "C"];
    val r = Thm.assume (Drule.list_implies ([A, B], C));
    val s = Thm.assume (Drule.mk_implies (A, B));
    val a = Thm.assume A;
  in
    Thm.implies_elim (Thm.implies_elim r a) (Thm.implies_elim s a)
    |> fold Thm.implies_intr [A, Thm.cprop_of s, Thm.cprop_of r]
    |> Drule.export_without_context
  end;

(*A ==> C from A ==> B ==> C and A ==> B, the propositions agreeing as they stand*)
fun follows th th' =
  let
    val [A, B] = Thm.cprems_of th;
    val inst = Vars.make (map (fn x => ((x, 0), propT)) ["A", "B", "C"] ~~ [A, B, Thm.cconcl_of th]);
  in Drule.implies_elim_list (Thm.instantiate (TVars.empty, inst) follows_rule) [th, th'] end;

(*t = P.truncate w is P.truncate source, or the source when it has that type already, for an
  instance w whose source has the layer P; under concept w, and under concept source unless that
  holds by a hidden field that is True or follows.  The steps keep the schematic variables of w*)
fun along_source ctxt P t w =
  let val thy = Proof_Context.theory_of ctxt in
    (case dest_head thy w of
      SOME (Instance_Head {source = SOME {layer, fields, forward, ...}, ...}, _, _) =>
        if not (member (op =) (layers_from thy layer) P) then NONE
        else
          let
            (*concept w ==> concept source ==> P.truncate w = P.truncate source*)
            val eq =
              at_layer #1 thy P layer (truncate_eq_of_fields thy layer fields)
              |> instantiate_at ctxt lhs_of t;
            val source = #2 (dest_comb (HOLogic.dest_Trueprop (nth (Thm.prems_of eq) 1)));
            val forward' = Option.map (instantiate_at ctxt premise_structure_of w) forward;
            (*concept source: by its hidden field, else from concept w; then concept w*)
            val eq1 =
              (case (concept_holds ctxt source, forward') of
                (SOME b, _) => Thm.implies_elim (Drule.rotate_prems 1 eq) b
              | (NONE, SOME th) => follows eq th
              | (NONE, NONE) => eq);
            val eq' =
              (case concept_holds ctxt w of SOME a => Thm.implies_elim eq1 a | NONE => eq1);
            val bare =
              Conv.concl_conv ~1
                (HOLogic.Trueprop_conv (Conv.arg_conv (Conv.rewr_conv (ident_of thy P))));
          in SOME (eq' |> fastype_of source = fastype_of t ? Conv.fconv_rule bare) end
    | _ => NONE)
  end;

(*t = P.truncate w rewritten: w has the type of t already; w is a truncation; w is an instance
  whose source has the layer P*)
fun truncate_proc ctxt P t w =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun rewritten th = SOME (meta (instantiate_at ctxt lhs_of t th));
  in
    if fastype_of w = fastype_of t then rewritten (#ident (the_laws thy P))
    else
      (case dest_truncation thy w of
        SOME (Q, _) => rewritten (truncate_merge thy P Q)
      | NONE => Option.map meta (along_source ctxt P t w))
  end;

(*concept (P.truncate u) = concept u*)
fun predicate_proc ctxt t w =
  let val thy = Proof_Context.theory_of ctxt in
    dest_truncation thy w |> Option.map (fn (P, _) =>
      meta (instantiate_at ctxt lhs_of t (#concept (the_laws thy P))))
  end;


(** truncate congruence rules **)

(*what a constant f does with a truncation at one of its arguments, O owning the type of that
  argument:
  Congruence: O.truncate ?T = O.truncate ?S ==> f ... ?T ... = f ... ?S ...;
  Commutes: f ... (P.truncate ?S) ... = P.truncate (f ... ?S ...) for the layer P = owner and
    every layer farther from the base, derived from the definition def of f for each P when it
    is met*)
datatype cong_rule = Congruence of thm | Commutes of {owner: string, def: thm};

(*a rule as it was declared: its stamp, and the stamps of the rules that it replaced, with
  those that they replaced*)
type cong_entry = {rule: cong_rule, stamp: stamp, replaced: stamp list};

(*the rule in use comes first: a theorem whose only premise is the one about the truncations,
  then the other theorems, each kind in the order of theorems*)
fun cong_ord (r, r') =
  let
    fun rank (Congruence th) = if Thm.nprems_of th = 1 then 0 else 1
      | rank (Commutes _) = 2;
  in
    (case (int_ord (rank r, rank r'), r, r') of
      (EQUAL, Congruence th, Congruence th') => Thm.thm_ord (th, th')
    | (ord, _, _) => ord)
  end;

(*by the constant and the position of the argument, from 0: the rules declared there that no
  later declaration has replaced.  A declaration replaces all that the theory has under the key;
  two theories of which neither has the other may each bring a rule, and both stay*)
structure Congs = Generic_Data
(
  type T = cong_entry list Inttab.table Symtab.table;
  val empty = Symtab.empty;
  fun merge tabs =
    Symtab.join (K (Inttab.join (K (fn (es, es') =>
      let
        val all = union (op = o apply2 #stamp) es es';
        fun replaced ({stamp, ...}: cong_entry) =
          exists (fn e: cong_entry => member (op =) (#replaced e) stamp) all;
      in filter_out replaced all end)))) tabs;
);

(*the number of arguments of the constant c in a rule of it*)
fun rule_arity _ _ (Congruence th) = length (#2 (strip_comb (lhs_of (Thm.prop_of th))))
  | rule_arity thy c (Commutes _) = length (binder_types (Sign.the_const_type thy c));

(*the rule in use: a theorem in the theory of the context; the definition of the mark Commutes
  stays without its theory, for the proofs in the home of its constant*)
fun truncate_cong context (c, i) =
  Symtab.lookup (Congs.get context) c
  |> Option.mapPartial (fn tab => Inttab.lookup tab i)
  |> Option.mapPartial (fn es: cong_entry list =>
    (case sort (cong_ord o apply2 #rule) es of
      {rule = Congruence th, ...} :: _ => SOME (Congruence (Thm.transfer'' context th))
    | e :: _ => SOME (#rule e)
    | [] => NONE));

(*the rule in use for the constant c applied to n arguments, at the position i: a rule speaks
  about the constant with all its arguments*)
fun rule_at context (c, i) n =
  truncate_cong context (c, i)
  |> Option.mapPartial
    (Option.filter (fn rule => rule_arity (Context.theory_of context) c rule = n));

(*a term rewritten: the definition def unfolded, then the selector Simpset, then for a constant
  of this package the fixed rules down to the leaves*)
fun cong_conv ctxt own def =
  Raw_Simplifier.rewrite_wrt ctxt false [def] then_conv
  Simplifier.rewrite (put_selector_simpset ctxt) then_conv
  (if own then unfold_conv ctxt [] else Thm.eta_conversion);

fun prove_cong_meta ctxt own def = prove_by_conv (cong_conv ctxt own def) ctxt;

fun prove_cong ctxt own def lhs rhs =
  prove_cong_meta ctxt own def lhs rhs
  |> Option.map (fn th => th RS @{thm meta_eq_to_obj_eq});

(*a constant of this package: its definition is unfolded down to the leaves*)
fun is_own thy c = is_some (head_of thy c);

(*the names of the arguments of a constant in the rules shown to users: those given, as for a
  view or an instance, else a, b, c*)
fun arg_names names n =
  let val used = ["T", "S", "r", "x"] in
    (case names of
      SOME names' => Name.variant_list used names'
    | NONE => Name.invent (Name.make_context used) "a" n)
  end;

(*the rule of a constant at the argument position i, from its definition; names: those of its
  arguments.  None when the more slot of the argument is no type variable, when that type
  variable is in the type of another argument, or when the two sides differ*)
fun derive_cong ctxt names {const = f, def, position = i} =
  let
    val thy = Proof_Context.theory_of ctxt;
    val own = is_own thy (dest_Const_name f);
    val (Ts, U) = strip_type (fastype_of f);
    val xs = map2 (fn T => fn x => Free (x, T)) Ts (arg_names names (length Ts));
    fun args x = nth_map i (K x) xs;
    val others = map (#1 o dest_Free) (nth_drop i xs);
  in
    (case dest_scheme_type thy (nth Ts i) of
      SOME (owner, Us, M as TFree (m, S)) =>
        let
          val occurs = exists_subtype (fn V => V = M);
          val truncate = mk_truncate thy owner;
          (*f at the types of the truncation of its argument*)
          val unit = Term.map_types (Term.typ_subst_atomic [(M, HOLogic.unitT)]);
          val r = Free ("r", nth Ts i);
          val truncated = list_comb (unit f, args (truncate r));
        in
          if exists occurs (Us @ nth_drop i Ts) then NONE
          else if not (occurs U) then
            prove_cong ctxt own def truncated (list_comb (f, args r))
            |> Option.map (fn eq =>
              let
                val n = singleton (Name.variant_list (m :: map #1 (Term.add_tfrees f []))) "'n";
                val other = Term.map_types (Term.typ_subst_atomic [(M, TFree (n, S))]);
                val T = Free ("T", nth Ts i) and S' = other (Free ("S", nth Ts i));
                val x = Free ("x", fastype_of (truncate r));
                val eq' = Drule.export_without_context eq;
              in
                Congruence
                  (lift thy others (T, S') truncate
                    (fn s => list_comb (if s aconv T then f else other f, args s))
                    (lambda x (list_comb (unit f, args x))) eq')
              end)
          else if U = nth Ts i then
            prove_cong ctxt own def truncated (truncate (list_comb (f, args r)))
            |> Option.map (K (Commutes {owner = owner, def = def}))
          else NONE
        end
    | _ => NONE)
  end;

fun derive_truncate_cong ctxt = derive_cong ctxt NONE;

(*c xs[i := P.truncate x] = P.truncate (c xs) as a meta equation, for variables xs of the types
  of args, x at the position i, where the constant c with the definition def has the mark
  Commutes*)
fun commuting ctxt def P c i args =
  let
    val truncate = mk_truncate (Proof_Context.theory_of ctxt) P;
    val xs = map_index (fn (k, u) => Var (("x", k), fastype_of u)) args;
    val x = nth xs i;
    val xs' = nth_map i (K (truncate x)) xs;
    val g = Const (c, map fastype_of xs ---> fastype_of x);
    val g' = Const (c, map fastype_of xs' ---> fastype_of (truncate x));
    fun prove ctxt' =
      prove_cong_meta ctxt' (is_own (Proof_Context.theory_of ctxt') c) (Thm.transfer' ctxt' def)
        (list_comb (g', xs')) (truncate (list_comb (g, xs)));
  in cached ctxt (list_comb (g', xs')) prove end;

(*c args[i := P.truncate u] = P.truncate (c args), where args has u at the position i*)
fun commuting_at ctxt def P c i args =
  commuting ctxt def P c i args |> Option.map (fn th =>
    let
      val inst =
        map_index (fn (k, u) => ((("x", k), fastype_of u), Thm.cterm_of ctxt u)) args;
    in Thm.instantiate (TVars.empty, Vars.make inst) th RS @{thm meta_eq_to_obj_eq} end);

(*ct = f args rewritten by a rule of f: at the first position with a rule whose argument is a
  truncation P.truncate u*)
fun cong_proc ctxt ct =
  let
    val thy = Proof_Context.theory_of ctxt;
    val t = Thm.term_of ct;
    val (f, args) = strip_comb t;
    fun apply (i, rule) =
      dest_truncation thy (nth args i) |> Option.mapPartial (fn (P, u) =>
        let
          val args' = nth_map i (K u) args;
          fun at T = list_comb (Const (dest_Const_name f, map fastype_of args' ---> T), args');
        in
          (case rule of
            Congruence th =>
              (let
                (*the two sides give ?T and ?S; the premise about them is two truncations
                  merged*)
                val th' =
                  instantiate_at ctxt sides_of (HOLogic.mk_prod (t, at (fastype_of t))) th;
                fun merged prem =
                  (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) prem of
                    SOME (twice as Const (c, _) $ a, Const (c', _) $ b) =>
                      if c = c' andalso a aconv nth args i andalso b aconv u
                      then Option.map (pair twice o #1) (dest_truncation thy twice) else NONE
                  | _ => NONE);
                val prems = Thm.prems_of th';
                val k = find_index (is_some o merged) prems;
              in
                if k < 0 then NONE
                else
                  let val (twice, owner) = the (merged (nth prems k)) in
                    SOME (meta (instantiate_at ctxt lhs_of twice (truncate_merge thy owner P)
                      RSN (k + 1, th')))
                  end
              end
              (*a rule for other arguments than those of t*)
              handle Pattern.MATCH => NONE)
          | Commutes {def, ...} =>
              Option.map (at_cterm ct) (commuting ctxt def P (dest_Const_name f) i args'))
        end);
  in
    (case f of
      Const (c, _) =>
        (case Symtab.lookup (Congs.get (Context.Proof ctxt)) c of
          SOME tab =>
            Inttab.keys tab |> get_first (fn i =>
              rule_at (Context.Proof ctxt) (c, i) (length args)
              |> Option.mapPartial (fn rule => apply (i, rule)))
        | NONE => NONE)
    | _ => NONE)
  end;


(** the more of a layer split **)

(*by the concept owning a layer, the next layer toward the base being L:
  (L.more ?X = L.more ?Y) = (the leaves of the layer agree and its more does)*)
structure Splits = Theory_Data
(
  type T = thm Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

(*the two sides of an equation between the more of a layer: what the layer of their type splits
  it into*)
fun split_proc ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    (case fastype_of (#1 (HOLogic.dest_eq t)) of
      Type (tyco, _) =>
        Symtab.lookup (#owners (Data.get thy)) tyco
        |> Option.mapPartial (Symtab.lookup (Splits.get thy))
        |> Option.mapPartial (fn th =>
          (*the two sides may be of two types*)
          SOME (meta (instantiate_at ctxt lhs_of t (Thm.transfer thy th)))
            handle Pattern.MATCH => NONE)
    | _ => NONE)
  end;


(** views given as a whole **)

(*x = y as a meta equation, for a view x and a structure y of its type with the same leaves and
  more; under concept y unless the hidden field of y is True*)
fun whole_equation ctxt x y =
  let val thy = Proof_Context.theory_of ctxt in
    (case (dest_scheme_type thy (fastype_of x), concept_holds ctxt x) of
      (SOME (L, Ts, _), SOME cx) =>
        let
          val both = @{lemma "P \<Longrightarrow> Q \<Longrightarrow> P = Q" by simp} OF [cx];
          val hidden = (case concept_holds ctxt y of SOME cy => both OF [cy] | NONE => both);
          fun same acc =
            prove_select ctxt (app thy acc x) (app thy acc y)
            |> Option.map (fn th => th RS @{thm meta_eq_to_obj_eq});
          val leaves =
            map (same o #acc) (flat_leaves thy (Ts, L)) @ [same (#more (the_entry thy L))];
        in
          if forall is_some leaves
          then SOME (meta (#equality (the_layer thy L) OF (hidden :: map the leaves)))
          else NONE
        end
    | _ => NONE)
  end;

(*ct: view constants applied to an instance to which the where clauses give the outermost of
  these views as a whole; it is the value given*)
fun whole ctxt ct =
  let
    fun views_of thy u views =
      (case dest_head thy u of
        SOME (View_Head {name, ...}, _, [w]) => views_of thy w (name :: views)
      | _ => (u, views));
    fun given thy t =
      let val (w, views) = views_of thy t [] in
        (case dest_head thy w of
          SOME (Instance_Head (inst as {wholes, ...}), T, args) =>
            Option.map (instance_term thy inst T args) (AList.lookup (op =) wholes views)
        | _ => NONE)
      end;
    val thy = Proof_Context.theory_of ctxt;
    val t = Thm.term_of ct;
  in
    if is_none (given thy t) then NONE
    else
      let
        val (key, _) = skeleton thy t [];
        fun prove ctxt' =
          given (Proof_Context.theory_of ctxt') key
          |> Option.mapPartial (whole_equation ctxt' key);
      in Option.map (at_cterm ct) (cached ctxt key prove) end
  end;


(** the simprocs **)

fun selector_proc ctxt ct =
  let
    val thy = Proof_Context.theory_of ctxt;
    val t = Thm.term_of ct;
    val selected =
      (case t of
        Const (c, _) $ w =>
          (case get_kind thy c of
            SOME (Leaf_Sel j) => select ctxt (fn thy' => leaf_value thy' j) ct
          | SOME (More_Sel d) => select ctxt (fn thy' => more_value thy' d) ct
          | SOME (Truncate P) => truncate_proc ctxt P t w
          | SOME Predicate => predicate_proc ctxt t w
          | SOME (View_Const _) => whole ctxt ct
          | NONE => NONE)
      | Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (Const (c, _) $ _) $ (Const (c', _) $ _) =>
          (case (c = c', get_kind thy c) of
            (true, SOME (More_Sel _)) => split_proc ctxt t
          | _ => NONE)
      | _ =>
          (case strip_comb t of
            (Const (c, _), _ :: _ :: _) =>
              (case get_kind thy c of
                SOME (Leaf_Sel j) => select_applied ctxt (fn thy' => leaf_value thy' j) ct
              | _ => NONE)
          | _ => NONE));
  in if is_some selected then selected else cong_proc ctxt ct end;

(*the constant c applied to n arguments*)
fun applied_to thy c n =
  let val f = const_of thy c in
    list_comb (f,
      take n (binder_types (fastype_of f))
      |> map_index (fn (k, T) => Free ("x" ^ string_of_int k, T)))
  end;

(*the numbers of arguments on which a constant has its simproc by its kind: one, the structure;
  for a leaf that is a function, also all arguments of the function*)
fun kind_arities thy c =
  (case get_kind thy c of
    SOME (Leaf_Sel _) =>
      (case length (binder_types (range_type (Sign.the_const_type thy c))) of
        0 => [1]
      | n => [1, n + 1])
  | SOME _ => [1]
  | NONE => []);

(*the simproc on these left sides, in the simpset and in the selector Simpset*)
fun add_selector_simproc name lhss context =
  let
    val add =
      Simplifier.add_proc (Simplifier.make_simproc (Context.proof_of context)
        {name = name, kind = Simplifier.Simproc, lhss = lhss, proc = K selector_proc,
         identifier = []});
  in context |> Simplifier.map_simpset add |> map_selector_simpset add end;

(*the split of the more of the layer below that of concept name, whose views are defined; its
  simproc on the equations at the type of this layer*)
fun add_split name thy =
  (case (#layer (the_entry thy name), layer_below thy name) of
    (SOME {rep_inject, leaves, ext, ...}, SOME below) =>
      let
        val {args, more, ...} = the_entry thy name;
        val p = (map TFree args, name);
        val T = scheme_type thy p (TFree (more_var (map #1 args)));
        val X = Free ("X", T) and Y = Free ("Y", T);
        fun same f = HOLogic.mk_eq (f X, f Y);
        val offset = leaf_count thy below;
        val lhs = same (app thy (#more (the_entry thy below)));
        val parts =
          map (fn k => same (read_leaf thy p (offset + k))) (0 upto length leaves - 1) @
            [same (app thy more)];
        val th =
          Goal.prove_sorry_global thy ["X", "Y"] []
            (mk_prop_eq (lhs, foldr1 HOLogic.mk_conj parts))
            (fn {context = ctxt, ...} =>
              rewrite_goals_tac ctxt [meta (rep_inject RS @{thm sym})] THEN
              CONVERSION (HOLogic.Trueprop_conv (unfold_conv ctxt [])) 1 THEN
              simp_tac
                (put_simpset HOL_basic_ss ctxt
                  |> Simplifier.add_simps @{thms prod_eq_iff conj_assoc}) 1 THEN
              TRY (resolve_tac ctxt @{thms refl} 1));
      in
        thy
        |> Splits.map (Symtab.update (name, Thm.trim_context th))
        |> Context.theory_map (add_selector_simproc ext [lhs])
      end
  | _ => thy);

(*a rule enters the table, in place of those that the context has at its position; it brings
  the constant's simproc on the arguments of the rule unless the constant has one on as many*)
fun add_truncate_cong (c, i) rule context =
  let
    val thy = Context.theory_of context;
    val arity = rule_arity thy c rule;
    val present =
      kind_arities thy c @
      (case Symtab.lookup (Congs.get context) c of
        SOME tab =>
          Inttab.fold (fn (_, es: cong_entry list) =>
            fold (cons o rule_arity thy c o #rule) es) tab []
      | NONE => []);
    val stored =
      (case rule of
        Congruence th => Congruence (Thm.trim_context th)
      | Commutes {owner, def} => Commutes {owner = owner, def = Thm.trim_context def});
    fun declared (old: cong_entry list) : cong_entry list =
      [{rule = stored, stamp = stamp (), replaced = maps (fn e => #stamp e :: #replaced e) old}];
  in
    context
    |> Congs.map (Symtab.map_default (c, Inttab.empty) (Inttab.map_default (i, []) declared))
    |> not (member (op =) present arity) ? add_selector_simproc c [applied_to thy c arity]
  end;

(*the rules of a view or instance constant with the given definition and names of its
  arguments, at the positions of its structure arguments*)
fun add_derived_congs f def names thy =
  let val ctxt = Proof_Context.init_global thy in
    thy |> fold_index (fn (i, _) =>
      (case derive_cong ctxt (SOME names) {const = f, def = def, position = i} of
        SOME rule => Context.theory_map (add_truncate_cong (dest_Const_name f, i) rule)
      | NONE => I)) names
  end;

(*a constant the simproc knows, with its simproc*)
fun register c kind thy =
  let val thy' = Kinds.map (Symtab.update (c, kind)) thy in
    thy' |> Context.theory_map
      (add_selector_simproc c (map (applied_to thy' c) (kind_arities thy' c)))
  end;

(*the selectors, more and truncate of the layer of concept name; the base's predicate is no
  selector*)
fun register_layer name thy =
  let
    val {parent, layer, more, ...} = the_entry thy name;
    val {leaves, truncate, ...} = the layer;
    val offset = (case parent of NONE => 0 | SOME p => length (flat_leaves thy p));
  in
    thy
    |> fold (fn (k, {name = SOME c, ...}: leaf) =>
          register c (if is_none parent then Predicate else Leaf_Sel (offset + k))
        | _ => I) (map_index I leaves)
    |> register (dest_Const_name more) (More_Sel name)
    |> register (dest_Const_name truncate) (Truncate name)
  end;


(** selector equations by name **)

(*for an instance w with a source: the layer L that it takes from it, and L.truncate w*)
fun source_step thy w =
  (case dest_head thy w of
    SOME (Instance_Head {source = SOME {layer, ...}, ...}, _, _) =>
      SOME (layer, mk_truncate thy layer w)
  | _ => NONE);

(*the step of an instance w along its source: L.truncate w is the source, truncated when it is
  wider; under concept w, and under concept of the source unless that holds or follows.  The
  truncation is on the left also where it is the identity*)
fun source_equation ctxt w =
  source_step (Proof_Context.theory_of ctxt) w
  |> Option.mapPartial (fn (layer, t) => along_source ctxt layer t w);

(*the same without the truncation on the left, for an instance w with the type of that layer.
  The step along the source that no truncation shows: simp does not rewrite with it*)
fun member_equation ctxt w =
  let val thy = Proof_Context.theory_of ctxt in
    source_step thy w |> Option.mapPartial (fn (layer, t) =>
      let
        val bare =
          Conv.concl_conv ~1
            (HOLogic.Trueprop_conv (Conv.arg1_conv (Conv.rewr_conv (ident_of thy layer))));
      in
        if fastype_of t <> fastype_of w then NONE
        else Option.map (Conv.fconv_rule bare) (along_source ctxt layer t w)
      end)
  end;

(*the equation that the selector simprocs give on t, with its premises concept _; else that
  between an instance and its source*)
fun selector_equation ctxt t =
  (case selector_proc ctxt (Thm.cterm_of ctxt t) of
    SOME th => SOME (th RS @{thm meta_eq_to_obj_eq})
  | NONE => member_equation ctxt t);

(*the equation named by a term; the variables that the context does not fix are schematic*)
fun named_equation ctxt t =
  let val ctxt' = Proof_Context.augment t ctxt in
    (case selector_equation ctxt' t of
      SOME th => Drule.zero_var_indexes (singleton (Variable.export ctxt' ctxt) th)
    | NONE => error ("No selector equation for " ^ quote (Syntax.string_of_term ctxt t)))
  end;

(*the structure t of a fact ... ==> C t or ... ==> C t = _*)
fun fact_structure thy th =
  let
    fun argument (_ $ t) = if is_some (dest_scheme_type thy (fastype_of t)) then SOME t else NONE
      | argument _ = NONE;
  in
    (case try (HOLogic.dest_Trueprop o Thm.concl_of) th of
      SOME (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ _) =>
        if fastype_of lhs = HOLogic.boolT then argument lhs else NONE
    | SOME t => argument t
    | NONE => NONE)
  end;

(*f t as Isabelle reads an application: an f that does not fit t is a type error*)
fun applied ctxt f t =
  Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
    (Term.map_types Type_Infer.paramify_vars f $ t);

(*on a fact C t the equation of the given selector on t; in [[...]] that of the given term*)
val _ =
  Theory.setup
    (Attrib.define_global \<^binding>\<open>concept_selector\<close>
      (fn src =>
        Attrib.attribute_syntax
          (Args.term_pattern >> (fn f =>
            Thm.rule_attribute [] (fn context => fn th =>
              let
                val ctxt = Context.proof_of context;
                val thy = Proof_Context.theory_of ctxt;
              in
                if Thm.is_dummy th then named_equation ctxt f
                else
                  (case fact_structure thy th of
                    SOME t => named_equation ctxt (applied ctxt f t)
                  | NONE =>
                      error ("Not a concept fact: " ^
                        quote (Syntax.string_of_term ctxt (Thm.prop_of th)) ^
                        Position.here (#2 (Token.name_of_src src)) ^ "\n" ^
                        "The expected form is \"C t\", such as \"group int.group\""))
              end)))
          src)
      "the equation of a selector on a structure" #> snd);


(** truncate congruence rules by name **)

(*the constant f and the position of the argument in a rule of the form
  C.truncate ?T = C.truncate ?S ==> f ... ?T ... = f ... ?S ..., other premises allowed*)
fun dest_cong thy th =
  let
    val prop = Thm.prop_of th;
    fun truncations prem =
      (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) prem of
        SOME (Const (c, _) $ (T as Var _), Const (c', _) $ (S as Var _)) =>
          (case (c = c' andalso T <> S, get_kind thy c) of
            (true, SOME (Truncate _)) => SOME (T, S)
          | _ => NONE)
      | _ => NONE);
    val pairs = map_filter truncations (Logic.strip_imp_prems prop);
  in
    (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop o Logic.strip_imp_concl) prop of
      SOME (lhs, rhs) =>
        (case (strip_comb lhs, strip_comb rhs) of
          ((Const (f, _), xs), (Const (g, _), ys)) =>
            if f <> g orelse length xs <> length ys then NONE
            else
              (case filter_out (op aconv o #2) (map_index I (xs ~~ ys)) of
                [(i, pair)] => if member (op =) pairs pair then SOME (f, i) else NONE
              | _ => NONE)
        | _ => NONE)
    | NONE => NONE)
  end;

(*a proved rule enters the table at the constant and position that its conclusion shows*)
fun declare_cong pos th context =
  let val ctxt = Context.proof_of context in
    (case dest_cong (Proof_Context.theory_of ctxt) th of
      SOME key => add_truncate_cong key (Congruence th) context
    | NONE =>
        error ("Not a truncate congruence rule: " ^
          quote (Syntax.string_of_term (Config.put show_question_marks false ctxt) (Thm.prop_of th)) ^
          Position.here pos ^ "\n" ^
          "The expected form is \"C.truncate ?T = C.truncate ?S \<Longrightarrow> " ^
          "f \<dots> ?T \<dots> = f \<dots> ?S \<dots>\", such as " ^
          "\"monoid.truncate ?T = monoid.truncate ?S \<Longrightarrow> " ^
          "monoid.Units ?T = monoid.Units ?S\""))
  end;

(*the rule of the constant written as s at its n-th structure argument, the first when no n is
  given; for the mark Commutes, the equation at the concept owning the type of the argument*)
fun named_cong context (s, n) =
  let
    val ctxt = Context.proof_of context;
    val thy = Proof_Context.theory_of ctxt;
    val c = dest_Const_name (Proof_Context.read_const {proper = true, strict = true} ctxt s);
    val Ts = binder_types (fastype_of (const_of thy c));
    val positions = filter (is_some o dest_scheme_type thy o nth Ts) (0 upto length Ts - 1);
    fun none () =
      error ("No truncate congruence rule for " ^
        (case n of SOME k => "argument " ^ string_of_int k ^ " of " | NONE => "") ^ quote s);
    val i = (case try (nth positions) (the_default 1 n - 1) of SOME i => i | NONE => none ());
  in
    (case truncate_cong context (c, i) of
      SOME (Congruence th) => th
    | SOME (Commutes {owner, def}) =>
        let
          val params =
            Option.map (map (#1 o dest_Free) o #params) (get_instance_entry thy c);
          val xs = map Free (arg_names params (length Ts) ~~ Ts);
        in
          (case commuting_at ctxt def owner c i xs of
            SOME th => Drule.export_without_context th
          | NONE => none ())
        end
    | NONE => none ())
  end;

(*on a lemma: the lemma becomes the rule of the constant in its conclusion; with a constant, in
  [[...]]: the rule of that constant*)
val _ =
  Theory.setup
    (Attrib.define_global \<^binding>\<open>truncate_cong\<close>
      (fn src =>
        Attrib.attribute_syntax
          (Scan.lift (Scan.option (Parse.embedded -- Scan.option Parse.nat)) >>
            (fn NONE => Thm.declaration_attribute (declare_cong (#2 (Token.name_of_src src)))
              | SOME arg => Thm.rule_attribute [] (fn context => fn _ => named_cong context arg)))
          src)
      "truncate congruence rule: declaration, or the rule of a constant" #> snd);


(** the fact trigger of Sledgehammer **)

(*a constant with a simproc: one that the simproc knows by its kind, or one with a rule*)
fun has_simproc ctxt c =
  is_some (get_kind (Proof_Context.theory_of ctxt) c) orelse
  Symtab.defined (Congs.get (Context.Proof ctxt)) c;

fun is_instance ctxt = is_some o get_instance_entry (Proof_Context.theory_of ctxt);

(*the applications in t on which a selector simproc may give an equation, and the instances;
  bound variables and the variables that the context does not fix are made schematic*)
fun redexes ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun between_mores (Const (c, _) $ _) (Const (c', _) $ _) =
          c = c' andalso (case get_kind thy c of SOME (More_Sel _) => true | _ => false)
      | between_mores _ _ = false;
    fun interesting (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ a $ b) = between_mores a b
      | interesting (u as _ $ _) =
          (case Term.head_of u of
            Const (c, _) => has_simproc ctxt c orelse is_instance ctxt c
          | _ => false)
      | interesting (Const (c, _)) = is_instance ctxt c
      | interesting _ = false;
    fun schematic Ts =
      Term.map_aterms
        (fn a as Free (x, T) => if Variable.is_fixed ctxt x then a else Var ((x, 0), T) | a => a)
      #> curry subst_bounds (map_index (fn (k, (x, T)) => Var ((x, k + 1), T)) Ts);
    fun add Ts u = interesting u ? insert (op aconv) (schematic Ts u);
    fun walk Ts (u as f $ a) = add Ts u #> walk Ts f #> walk Ts a
      | walk Ts (Abs (x, T, b)) = walk ((x, T) :: Ts) b
      | walk Ts u = add Ts u;
  in walk [] t [] end;

(*for the constants that became relevant: a constant with a simproc applied to an instance, a
  view or a truncation, the arguments of these schematic; and such an instance alone*)
fun pairs ctxt news rels =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun inner c =
      (case head_of thy c of
        NONE => NONE
      | SOME head =>
          let
            val f = Logic.varify_global (const_of thy c);
            val names =
              (case head of
                Instance_Head {params, ...} => map (#1 o dest_Free) params
              | View_Head _ => ["S"]
              | Truncate_Head _ => ["r"]);
            val Ts = take (length names) (binder_types (fastype_of f));
          in SOME (c, list_comb (f, map2 (fn x => fn T => Var ((x, 0), T)) names Ts)) end);
    val inners = map_filter inner rels;
    val new = member (op =) news;
    fun pair f (c, w) =
      if new f orelse new c
      then (SOME (app thy (const_of thy f) w) handle Type.TYPE_MATCH => NONE)
      else NONE;
  in
    maps (fn f => map_filter (pair f) inners) (filter (has_simproc ctxt) rels) @
    map_filter (fn (c, w) => if new c andalso is_instance ctxt c then SOME w else NONE) inners
  end;

(*a term as a candidate of MePo, when the name written for it denotes an equation*)
fun candidate ctxt t =
  let
    val s = Sledgehammer_Util.hackish_string_of_term ctxt t;
    val name =
      "[[concept_selector " ^ (if exists_string (fn c => c = "\"") s then cartouche s else quote s) ^
        "]]";
  in
    (case try (Sledgehammer_Util.thms_of_name ctxt) name of
      SOME [th] =>
        SOME {name = name, prop = Thm.prop_of th,
          stature = (ATP_Problem_Generate.Global, ATP_Problem_Generate.Simp)}
    | _ => NONE)
  end;

val _ =
  Theory.setup (Context.theory_map (Sledgehammer_MePo.add_trigger "concept_selector"
    (fn {ctxt, hyp_ts, concl_t, new_consts, rel_consts, accepted} =>
      if exists (fn c => has_simproc ctxt c orelse is_instance ctxt c) new_consts then
        (*the terms of the goal before the first round; the pairs in every round*)
        ((if null accepted then maps (redexes ctxt) (concl_t :: hyp_ts) else []) @
          pairs ctxt new_consts (Symtab.keys rel_consts))
        |> distinct (op aconv)
        |> map_filter (candidate ctxt)
      else [])));



(** two truncations made equal **)

(* the comparison, on terms *)

datatype step =
  Strip of string  (*from P.truncate u to u*)
| Along of source;  (*from an instance to its source*)

(*the terms walked through with the step leaving each, and the end*)
type walk = (term * step) list * term;

(*what joins two arguments that differ of two terms with the same head*)
datatype arg =
  Whole of term * term * (int * arg) list
    (*the arguments are equal: they have the same head, and theirs are joined in turn*)
| Rule of thm * level  (*a Congruence rule, the arguments made equal at its layer*)
(*what joins the ends of the two walks of a level*)
and ends =
  Same  (*they are equal under the instantiation*)
| Joined of (int * arg) list * {position: int, out: thm * thm, inside: level} option
    (*they have the same head: what joins the arguments that differ; and at one more position
      the truncation at the layer of inside moves out of both, by the equations out*)
(*layer.truncate a = layer.truncate b: the walks from a and from b, and what joins their ends*)
and level = Level of {layer: string, a: term, b: term, left: walk, right: walk, ends: ends};

fun went_along ((nodes, _): walk) = exists (fn (_, Along _) => true | _ => false) nodes;

(*the arguments joined at the ends, and the level inside a position where the truncation moves
  out*)
fun dest_ends Same = ([], [])
  | dest_ends (Joined (args, moved)) =
      (args, (case moved of SOME {inside, ...} => [inside] | NONE => []));

(*the source src of an instance at the type T of its constant, applied to args*)
fun source_at thy inst T args ({term, ...}: source) = instance_term thy inst T args term;

(*from u toward the base: out of truncations, and along the sources that have the layer L*)
fun walk thy L u : walk =
  let
    fun step s u' = let val (nodes, e) = walk thy L u' in ((u, s) :: nodes, e) end;
  in
    (case dest_head thy u of
      SOME (Truncate_Head P, _, [u']) => step (Strip P) u'
    | SOME (Instance_Head (inst as {source = SOME (src as {layer, ...}), ...}), T, args) =>
        if member (op =) (layers_from thy layer) L
        then step (Along src) (source_at thy inst T args src) else ([], u)
    | _ => ([], u))
  end;

(*the type T made U by an instantiation that extends env*)
fun matches_type thy (T, U) ((tyenv, tenv): Type.tyenv * Envir.tenv) =
  SOME (Sign.typ_match thy (T, U) tyenv, tenv) handle Type.TYPE_MATCH => NONE;

(*the layer of a Congruence rule with the truncations as its only premise*)
fun rule_layer thy th =
  (case Thm.prems_of th of
    [prem] => Option.map #1 (dest_truncation thy (lhs_of prem))
  | _ => NONE);

(*f xs with z at the position k, f at the type that fits*)
fun replaced u k z =
  let val (f, xs) = strip_comb u; val xs' = nth_map k (K z) xs
  in list_comb (Const (dest_Const_name f, map fastype_of xs' ---> fastype_of u), xs') end;

(*L.truncate a = L.truncate b under an instantiation of the variables of a that extends env: the
  first terms on the two walks that match, by the number of steps; else the ends of the walks
  joined at their arguments*)
fun connect ctxt L (a, b) env =
  let
    val thy = Proof_Context.theory_of ctxt;
    val a' = instantiated env a;
    val (lnodes, lend) = walk thy L a';
    val (rnodes, rend) = walk thy L b;
    val ls = map #1 lnodes @ [lend] and rs = map #1 rnodes @ [rend];
    fun level i j ends =
      Level {layer = L, a = a', b = b, left = (take i lnodes, nth ls i),
        right = (take j rnodes, nth rs j), ends = ends};
    val pairs =
      maps (fn n => map_filter (fn i =>
        if i < length ls andalso n - i < length rs then SOME (i, n - i) else NONE) (0 upto n))
        (0 upto length lnodes + length rnodes);
    (*where a walk takes its first step along a source, else its end: up to there nothing needs
      the concept of the two terms*)
    fun before nodes =
      (case find_index (fn (_, Along _) => true | _ => false) nodes of
        ~1 => length nodes
      | i => i);
    fun joined (i, j) =
      join ctxt (SOME L) (nth ls i, nth rs j) env |> Option.map (apsnd (level i j));
  in
    (case get_first (fn (i, j) =>
        Option.map (rpair (level i j Same)) (matches thy (nth ls i, nth rs j) env)) pairs of
      NONE =>
        get_first joined
          (distinct (op =) [(before lnodes, before rnodes), (length lnodes, length rnodes)])
    | met => met)
  end

(*two terms with the same head joined at their arguments, under an instantiation that extends
  env; layer: an equation between their truncations at this layer will do, so that at one
  position the truncation may move out of both.  What is accepted here, the proof can build: a
  rule is taken where it fits, a mark Commutes where its equations are derived*)
and join ctxt layer (x, y) env =
  (case (strip_comb x, strip_comb y) of
    ((Const (c, _), xs), (Const (d, _), ys)) =>
      if c <> d orelse length xs <> length ys then NONE
      else
        let
          val thy = Proof_Context.theory_of ctxt;
          (*what the proof has made of x when it comes to the position k: the arguments of y
            before k*)
          fun current (env: Type.tyenv * Envir.tenv) k =
            let val args = take k ys @ map (instantiated env) (drop k xs) in
              list_comb
                (Const (c, map fastype_of args ---> Envir.norm_type (#1 env) (fastype_of x)), args)
            end;
          fun arg (k, (x_k0, y_k)) (SOME (env, joined, moved)) =
                let
                  val x_k = instantiated env x_k0;
                  fun whole () =
                    (case join ctxt NONE (x_k, y_k) env of
                      SOME (env', Joined (args, NONE)) =>
                        SOME (env', (k, Whole (x_k, y_k, args)) :: joined, moved)
                    | _ => NONE);
                in
                  (case matches thy (x_k, y_k) env of
                    SOME env' => SOME (env', joined, moved)
                  | NONE =>
                      (case (rule_at (Context.Proof ctxt) (c, k) (length xs), layer, moved) of
                        (SOME (Congruence th), _, _) =>
                          (case rule_layer thy th of
                            SOME L =>
                              (case connect ctxt L (x_k, y_k) env of
                                SOME (env', lev) =>
                                  (*the types of the two arguments are known now*)
                                  let val cur = current env' k in
                                    if fits thy sides_of
                                      (HOLogic.mk_prod (cur, replaced cur k y_k)) th
                                    then SOME (env', (k, Rule (th, lev)) :: joined, moved)
                                    else whole ()
                                  end
                              | NONE => NONE)
                          | NONE => whole ())
                      | (SOME (Commutes {owner, def}), SOME L, NONE) =>
                          let
                            val P = if member (op =) (layers_from thy L) owner then L else owner;
                            (*the truncation moved out of c at the arguments of y, with u at k*)
                            fun out u = commuting ctxt def P c k (nth_map k (K u) ys);
                          in
                            (case connect ctxt P (x_k, y_k) env of
                              SOME (env', lev) =>
                                (case (out (instantiated env' x_k), out y_k) of
                                  (SOME out_x, SOME out_y) =>
                                    SOME (env', joined,
                                      SOME {position = k, out = (out_x, out_y), inside = lev})
                                | _ => whole ())
                            | NONE => NONE)
                          end
                      | _ => whole ()))
                end
            | arg _ NONE = NONE;
        in
          fold arg (map_index I (xs ~~ ys)) (SOME (env, [], NONE))
          |> Option.mapPartial (fn (env', joined, moved) =>
            (*no truncation moves out: the two terms become one, so they have one type*)
            (if is_some moved then SOME env'
             else matches_type thy (fastype_of x, fastype_of y) env')
            |> Option.map (rpair (Joined (rev joined, moved))))
        end
  | _ => NONE);


(* which structures are legal *)

(*an equation of the comparison between x and y, usable once the structures in needs are
  legal*)
datatype origin = Of_Level of level | Of_Ends of level | Of_Whole of term * term * (int * arg) list;
type equation = {needs: term list, x: term, y: term, origin: origin};

(*the two ends of the levels that went along a source, under the instantiation inst: what the
  equations of the comparison need*)
fun needs_args inst args = maps (needs_arg inst o #2) args
and needs_arg inst (Whole (_, _, args)) = needs_args inst args
  | needs_arg inst (Rule (_, lev)) = needs_level inst lev
and needs_ends inst ends =
  let val (args, levs) = dest_ends ends in needs_args inst args @ maps (needs_level inst) levs end
and needs_level inst (Level {a, b, left, right, ends, ...}) =
  (if went_along left orelse went_along right then [inst a, b] else []) @ needs_ends inst ends;

fun equations_args inst args = maps (equations_arg inst o #2) args
and equations_arg inst (Whole (x, y, args)) =
      {needs = needs_args inst args, x = inst x, y = y, origin = Of_Whole (x, y, args)} ::
        equations_args inst args
  | equations_arg inst (Rule (_, lev)) = equations_level inst lev
and equations_ends inst ends =
  let val (args, levs) = dest_ends ends
  in equations_args inst args @ maps (equations_level inst) levs end
and equations_level inst (lev as Level {a, b, left, right, ends, ...}) : equation list =
  {needs = needs_level inst lev, x = inst a, y = b, origin = Of_Level lev} ::
  {needs = needs_ends inst ends, x = inst (#2 left), y = #2 right, origin = Of_Ends lev} ::
    equations_ends inst ends;

(*the terms on the walks of the comparison*)
fun terms_args inst args = maps (terms_arg inst o #2) args
and terms_arg inst (Whole (x, y, args)) = inst x :: y :: terms_args inst args
  | terms_arg inst (Rule (_, lev)) = terms_level inst lev
and terms_ends inst ends =
  let val (args, levs) = dest_ends ends in terms_args inst args @ maps (terms_level inst) levs end
and terms_level inst (Level {left = (lnodes, lend), right = (rnodes, rend), ends, ...}) =
  map (inst o #1) lnodes @ [inst lend] @ map #1 rnodes @ [rend] @ terms_ends inst ends;

(*why a structure u is legal*)
datatype reason =
  Start
| Hidden_True of thm  (*an instance or a view whose hidden field is True, by its theorem*)
| Hidden_Same of thm * term * thm
    (*an instance with the hidden field of this legal instance: the theorems of the two*)
| Truncates of string * term  (*u is P.truncate v for this legal v*)
| Truncated of string * term  (*this legal structure is P.truncate u*)
| Implied of term * thm
    (*by this implication of this legal instance: u is its source, or one of its arguments*)
| Equation of equation * term;  (*by the other side of an equation*)

val legal = AList.defined (op aconv);

(*the structures that are legal when the starts are, among the candidates and what follows
  from them, each with the reason: the least set of CONCEPT_OWN_TYPE_PLAN 3.13, step 6*)
fun legal_from thy candidates (equations: equation list) starts : (term * reason) list =
  let
    fun follows u =
      (case dest_head thy u of
        SOME (Truncate_Head P, _, [u']) => [(u', Truncated (P, u))]
      | SOME (Instance_Head (inst as {source, implications, ...}), T, args) =>
          (case source of
            SOME (src as {forward = SOME th, ...}) =>
              [(source_at thy inst T args src, Implied (u, th))]
          | _ => []) @
          map (fn (i, th) => (nth args i, Implied (u, th))) (Inttab.dest implications)
      | _ => []);
    fun add (u, reason) known =
      if legal known u then known else fold add (follows u) ((u, reason) :: known);
    fun enters known u =
      if legal known u then NONE
      else
        (case dest_truncation thy u of
          SOME (P, u') => if legal known u' then SOME (u, Truncates (P, u')) else NONE
        | NONE =>
            (case hidden_field thy u of
              SOME (th, \<^Const_>\<open>True\<close>) => SOME (u, Hidden_True th)
            | SOME (th, H) =>
                known |> get_first (fn (v, _) =>
                  (case hidden_field thy v of
                    SOME (th', H') =>
                      if H aconv H' then SOME (u, Hidden_Same (th, v, th')) else NONE
                  | NONE => NONE))
            | NONE => NONE));
    fun by_equation known (eq as {needs, x, y, ...}) =
      if not (forall (legal known) needs) then NONE
      else if legal known x andalso not (legal known y) then SOME (y, Equation (eq, x))
      else if legal known y andalso not (legal known x) then SOME (x, Equation (eq, y))
      else NONE;
    fun saturate known =
      (case get_first (enters known) candidates of
        SOME new => saturate (add new known)
      | NONE =>
          (case get_first (by_equation known) equations of
            SOME new => saturate (add new known)
          | NONE => known));
  in saturate (fold (fn u => add (u, Start)) starts []) end;


(* the theorem *)

(*f x = f y from x = y*)
fun cong ctxt f th =
  let
    val T = fastype_of (lhs_of (Thm.prop_of th));
    val z = singleton (Name.variant_list (Term.add_free_names (f (Const ("", T))) [])) "z";
    val g = lambda (Free (z, T)) (f (Free (z, T)));
  in Drule.infer_instantiate ctxt [(("f", 0), Thm.cterm_of ctxt g)] @{thm arg_cong} OF [th] end;

(*the theorem of a comparison whose terms have no schematic variables: the equation of top,
  under the hypotheses concept u for the starts u of known*)
fun prove_truncate_eq ctxt inst known (top: level) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ct = Thm.cterm_of ctxt;
    val concept_prop = HOLogic.mk_Trueprop o mk_concept thy;
    val base_more = mk_base_more thy;
    fun refl u =
      Thm.instantiate' [SOME (Thm.ctyp_of ctxt (fastype_of u))] [SOME (ct u)] @{thm refl};
    fun trans th1 th2 = @{thm trans} OF [th1, th2];
    fun sym th = th RS @{thm sym};

    (*x = x with the arguments ys at the positions joined*)
    fun args_eq x ys joined =
      let
        fun at (k, arg) th =
          let
            val cur = rhs_of (Thm.prop_of th);
            val step =
              (case arg of
                Whole (x_k, y_k, args) => cong ctxt (replaced cur k) (whole_eq x_k y_k args)
              | Rule (rule, lev) =>
                  instantiate_at ctxt sides_of
                    (HOLogic.mk_prod (cur, replaced cur k (nth ys k))) rule OF [level_eq lev]);
          in trans th step end;
      in fold at joined (refl x) end

    and whole_eq x y args = args_eq (inst x) (#2 (strip_comb y)) args

    (*L.truncate x = L.truncate y for the ends of two walks*)
    and ends_eq L x y ends =
      let val truncate = mk_truncate thy L in
        (case ends of
          Same => refl (truncate y)
        | Joined (args, NONE) => cong ctxt truncate (args_eq x (#2 (strip_comb y)) args)
        | Joined (args, SOME {position = k, out = (out_x, out_y), inside}) =>
            let
              val Level {layer = P, ...} = inside;
              val truncate' = mk_truncate thy P;
              (*the other arguments first; then the truncation moved out on both sides*)
              val rest = args_eq x (#2 (strip_comb y)) args;
              fun out th u =
                instantiate_at ctxt rhs_of (truncate' u) (th RS @{thm meta_eq_to_obj_eq});
              val out_x' = out out_x (rhs_of (Thm.prop_of rest));
              val inner =
                cong ctxt (replaced (lhs_of (Thm.prop_of out_x')) k) (level_eq inside);
              val moved = trans (sym out_x') (trans inner (out out_y y));
            in at_layer #1 thy L P (trans (cong ctxt truncate' rest) moved) end)
      end

    (*L.truncate a = L.truncate b; when a walk went along a source, under concept a, concept b*)
    and level_eq (Level {layer = L, a, b, left, right, ends}) =
      let
        val truncate = mk_truncate thy L;
        val more = base_more o truncate;
        val (lnodes, lend) = (map (apfst inst) (#1 left), inst (#2 left));
        val (rnodes, rend) = right;
        val joined = ends_eq L lend rend ends;
        fun strip (u, P) = instantiate_at ctxt lhs_of (truncate u) (truncate_merge thy L P);
      in
        if went_along left orelse went_along right then
          let
            fun step (u, Strip P) = cong ctxt base_more (strip (u, P))
              | step (u, Along {layer, fields, ...}) =
                  instantiate_at ctxt lhs_of (more u) (at_layer #2 thy L layer fields);
            fun along u nodes =
              fold (fn node => fn th => trans th (step node)) nodes (refl (more u));
            val fields =
              trans (trans (along (inst a) lnodes) (cong ctxt base_more joined))
                (sym (along b rnodes));
          in
            truncate_eq_of_fields thy L fields
              OF map (Thm.assume o ct o concept_prop) [inst a, b]
          end
        else
          let
            fun along u nodes =
              fold (fn (v, Strip P) => (fn th => trans th (strip (v, P))) | _ => I) nodes
                (refl (truncate u));
          in trans (trans (along (inst a) lnodes) joined) (sym (along b rnodes)) end
      end;

    (*concept x = concept y from an equation, under concept u for its needs*)
    fun concept_eq ({x, y, origin, ...}: equation) =
      let
        fun untruncated L th =
          let
            val law = #concept (the_laws thy L);
            fun at u = instantiate_at ctxt lhs_of (mk_concept thy (mk_truncate thy L u)) law;
          in trans (sym (at x)) (trans (cong ctxt (mk_concept thy) th) (at y)) end;
      in
        (case origin of
          Of_Level (lev as Level {layer, ...}) => untruncated layer (level_eq lev)
        | Of_Ends (Level {layer, left, right, ends, ...}) =>
            untruncated layer (ends_eq layer (inst (#2 left)) (#2 right) ends)
        | Of_Whole (x', y', args) => cong ctxt (mk_concept thy) (whole_eq x' y' args))
      end;

    fun law P = #concept (the_laws thy P);

    (*concept u, under the hypotheses concept v for the starts v*)
    fun concept u =
      (case the (AList.lookup (op aconv) known u) of
        Start => Thm.assume (ct (concept_prop u))
      | Hidden_True th => hidden_at ctxt u th RS @{thm eqTrueE}
      | Hidden_Same (th, v, th') =>
          @{thm iffD2} OF [hidden_at ctxt u th, @{thm iffD1} OF [hidden_at ctxt v th', concept v]]
      | Truncates (P, v) =>
          instantiate_at ctxt structure_of u (law P RS @{thm iffD2}) OF [concept v]
      | Truncated (P, v) =>
          instantiate_at ctxt premise_structure_of v (law P RS @{thm iffD1}) OF [concept v]
      | Implied (v, th) => instantiate_at ctxt premise_structure_of v th OF [concept v]
      | Equation (eq as {x, ...}, v) =>
          (if v aconv x then @{thm iffD1} else @{thm iffD2})
            OF [given eq (concept_eq eq), concept v])

    (*a theorem without its hypotheses concept u for the structures needed, which are legal*)
    and given ({needs, ...}: equation) th = without needs th
    and without needs th =
      fold (fn u => fn th' =>
        Thm.implies_elim (Thm.implies_intr (ct (concept_prop u)) th') (concept u))
        (distinct (op aconv) needs) th;
  in without (needs_level inst top) (level_eq top) end;


(* truncate_eq *)

(*for terms t without schematic variables*)
fun truncate_eq_fixed ctxt {concept, s, t} =
  let
    val thy = Proof_Context.theory_of ctxt;
    val L = #owner (the_entry thy concept);
  in
    connect ctxt L (s, t) (Vartab.empty, Vartab.empty)
    |> Option.mapPartial (fn (env as (tyenv, tenv), top) =>
      if not (forall (Vartab.defined tenv o #1) (Term.add_vars s []) andalso
        forall (Vartab.defined tyenv o #1) (Term.add_tvars s []))
      then NONE
      else
        let
          val inst = instantiated env;
          val s' = inst s;
          val needs = needs_level inst top;
          val equations = equations_level inst top;
          val terms = terms_level inst top;
          val candidates =
            distinct (op aconv)
              (terms @ maps (fn u =>
                (case dest_truncation thy u of SOME (_, u') => [u'] | NONE => [])) terms);
          val legal_from = legal_from thy candidates equations;
          val concept_prop = Thm.cterm_of ctxt o HOLogic.mk_Trueprop o mk_concept thy;
          (*the instantiation in the form that matching s gives: the variables at their types
            in s*)
          val env' =
            (tyenv,
              Vartab.build (Term.add_vars s [] |> fold (fn (xi, T) =>
                Vartab.update (xi, (T, #2 (the (Vartab.lookup tenv xi)))))));
          fun result extra known =
            {env = env', extra = extra,
             eq = Lazy.lazy (fn () =>
              prove_truncate_eq ctxt inst known top
              |> (case extra of SOME u => Thm.implies_intr (concept_prop u) | NONE => I)
              |> Thm.implies_intr (concept_prop s')),
             reached = legal (legal_from [t]) s'};
          val from_s = legal_from [s'];
        in
          if forall (legal from_s) needs then SOME (result NONE from_s)
          else
            let val from_both = legal_from [s', t] in
              if forall (legal from_both) needs then SOME (result (SOME t) from_both) else NONE
            end
        end)
  end;

(*concept s' ==> O.truncate s' = O.truncate t, or with a second premise concept t (extra), for
  the layer O owning the type of the concept, and s' the instance of s under env; reached:
  concept t gives concept s'.  The variables of s are apart from those of t, which stay*)
fun truncate_eq ctxt (arg as {concept, s, t}) =
  if Term.maxidx_of_term t = ~1 then truncate_eq_fixed ctxt arg
  else
    let
      val (inst, ctxt') = Variable.import_inst true [t] ctxt;
      (*back to the variables of t*)
      val (revertT, revert) = Variable.import_inst_revert inst;
      val thaw = Term_Subst.instantiate_frees (revertT, revert);
      val thawT = Term_Subst.instantiateT_frees revertT;
      val thaw_thm =
        Thm.instantiate_frees
          (TFrees.map (K (Thm.ctyp_of ctxt)) revertT, Frees.map (K (Thm.cterm_of ctxt)) revert);
    in
      truncate_eq_fixed ctxt' {concept = concept, s = s, t = Term_Subst.instantiate inst t}
      |> Option.map (fn {env = (tyenv, tenv), eq, extra, reached} =>
        {env =
          (Vartab.map (K (apsnd thawT)) tyenv,
            Vartab.map (K (fn (T, u) => (thawT T, thaw u))) tenv),
         eq = Lazy.map thaw_thm eq,
         extra = Option.map thaw extra, reached = reached})
    end;



(** equality as users see it **)

(*by the concept owning a layer: concept ?x ==> concept ?y ==> the leaves with names agree ==>
  the views holding leaves agree ==> the more of the layer agrees ==> ?x = ?y; in the order of
  the leaves, a view at its first leaf*)
structure Equalities = Theory_Data
(
  type T = thm Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);

fun equality thy name =
  Symtab.lookup (Equalities.get thy) (#owner (the_entry thy name))
  |> Option.map (Thm.transfer thy);

(*for the layer of concept name, whose views are defined*)
fun add_equality name thy =
  (case #layer (the_entry thy name) of
    NONE => thy
  | SOME {equality, ...} =>
      let
        val {args, more, ...} = the_entry thy name;
        val p = (map TFree args, name);
        val T = scheme_type thy p (TFree (more_var (map #1 args)));
        val x = Free ("x", T) and y = Free ("y", T);
        fun same f = mk_prop_eq (f x, f y);
        val leaves = flat_leaves thy p;
        (*a leaf without a name: the view holding it, with the leaf's place in the view*)
        val held =
          map_index (fn (k, {name = SOME _, ...}: flat_leaf) => (k, NONE)
            | (k, _) =>
                let val (_, const, parent, r) = holder thy p k
                in (k, SOME (const, parent, r)) end) leaves;
        val prems =
          map (HOLogic.mk_Trueprop o mk_concept thy) [x, y] @
          distinct (op aconv)
            (map (fn (k, NONE) => same (read_leaf thy p k)
              | (_, SOME (const, _, _)) => same (app thy const)) held) @
          [same (app thy more)];
        val th =
          Goal.prove_sorry_global thy ["x", "y"] prems (mk_prop_eq (x, y))
            (fn {context = ctxt, prems = facts} =>
              let
                fun fact prop = the (find_first (fn th => Thm.prop_of th aconv prop) facts);
                val [cx, cy] = map (fact o HOLogic.mk_Trueprop o mk_concept thy) [x, y];
                (*the leaf of both sides is that leaf of the view, which agrees*)
                fun leaf (k, NONE) = fact (same (read_leaf thy p k))
                  | leaf (k, SOME (const, parent, r)) =
                      let
                        val read = read_leaf thy parent r;
                        fun through z =
                          the (prove_select ctxt (app thy (#acc (nth leaves k)) z)
                            (read (app thy const z))) RS @{thm meta_eq_to_obj_eq};
                        val views = cong ctxt read (fact (same (app thy const)));
                      in
                        @{thm trans} OF
                          [through x, @{thm trans} OF [views, through y RS @{thm sym}]]
                      end;
              in
                resolve_tac ctxt [equality] 1 THEN resolve_tac ctxt @{thms iffI} 1 THEN
                EVERY (map (fn th => resolve_tac ctxt [th] 1)
                  (cy :: cx :: map leaf held @ [fact (same (app thy more))]))
              end);
      in Equalities.map (Symtab.update (name, Thm.trim_context th)) thy end);

(** definitions **)

(*concept lhs = constraint and the code equation lhs = value, from the sealed definition of
  lhs's head as a lambda over xs*)
fun prove_definitional thy def xs lhs constraint value =
  let
    val base = base_name thy;
    val base_conv = #conv (hd (#leaves (the_layer thy base)));
    fun prove prop tac = Goal.prove_sorry_global thy xs [] (HOLogic.mk_Trueprop prop) tac;
    val concept_eq =
      prove (HOLogic.mk_eq (Const (base, fastype_of lhs --> HOLogic.boolT) $ lhs, constraint))
        (fn {context = ctxt, ...} =>
          rewrite_goals_tac ctxt [def, meta base_conv] THEN resolve_tac ctxt @{thms refl} 1);
    val code_eq =
      prove (HOLogic.mk_eq (lhs, value))
        (fn {context = ctxt, ...} =>
          rewrite_goals_tac ctxt [def] THEN resolve_tac ctxt @{thms refl} 1);
  in (concept_eq, code_eq) end;


(** declaring a concept **)

datatype item =
  Field of binding * typ
| View of {qualifier: binding, parent: parent, more: typ,
    where_: ((string * Position.T) list * string) list};


(* layers *)

(*the abbreviations C_scheme and C for the type of a concept*)
fun abbrev_types b args zeta sT =
  Typedecl.abbrev_global (Binding.suffix_name "_scheme" b, map #1 (args @ [zeta]), NoSyn) sT
  #> snd #>
  Typedecl.abbrev_global (b, map #1 args, NoSyn)
    (Term.typ_subst_atomic [(TFree zeta, HOLogic.unitT)] sT) #> snd;

(*concept b with a new layer over its parent, entered and its selectors registered; the leaves
  are named or anonymous (empty binding); a named leaf is the constant C.f, or the unqualified f
  for the base's predicate*)
fun add_layer b args parent bleaves thy0 =
  let
    val name = Sign.full_name thy0 b;
    val is_base = is_none parent;
    val Ts = map snd bleaves;
    val n = length Ts;
    val zeta = more_var (map #1 args);
    val moreT = TFree zeta;
    val repT = layerT (Ts @ [moreT]);
    val ext_args = filter (member (op =) (fold Term.add_tfreesT Ts [])) args @ [zeta];
    val qualified = Sign.qualified_path true b;

    (* the extension type *)
    val ext_b = Binding.name "extension";
    val {Rep_name = Rb, Abs_name = Ab, type_definition_name = Tb} = Typedef.default_bindings ext_b;
    val ((ext_tyco, ({Rep_name, Abs_name, ...},
        {Abs_inverse, Rep_inverse, Rep_inject, Abs_cases, Rep_cases, Abs_induct, Rep_induct,
          ...})), thy1) =
      thy0
      |> qualified
      |> Typedef.add_typedef_global {overloaded = false}
        (ext_b, ext_args, NoSyn) (HOLogic.mk_UNIV repT)
        (SOME {Rep_name = hidden Rb, Abs_name = hidden Ab, type_definition_name = hidden Tb})
        (fn ctxt => resolve_tac ctxt @{thms UNIV_witness} 1);
    (*typedef registers its cases and induct rules with Induct: take them out again*)
    val thy1 = thy1
      |> Sign.restore_naming thy0
      |> Context.theory_map
       (fold (Thm.attribute_declaration Induct.cases_del) [Abs_cases, Rep_cases] #>
        fold (Thm.attribute_declaration Induct.induct_del) [Abs_induct, Rep_induct]);
    val extT = Type (ext_tyco, map TFree ext_args);
    val abs = Const (Abs_name, repT --> extT);
    val rep = Const (Rep_name, extT --> repT);
    val abs_inverse = Abs_inverse OF @{thms UNIV_I};

    (* the scheme type: the parent's, its more slot filled with extT *)
    val sT = (case parent of NONE => extT | SOME p => scheme_type thy1 p extT);
    val thy1 = abbrev_types b args zeta sT thy1;
    val r = Free ("r", sT);
    val rep_r =
      rep $ (case parent of NONE => r | SOME (_, p) => app thy1 (#more (the_entry thy1 p)) r);
    val accs = map (lambda r) (projs (n + 1) rep_r);

    (* constants for the named leaves and for more, with their sealed definitions *)
    val named =
      map (fn (x, _) => if Binding.is_empty x then NONE else SOME x) bleaves @
        [SOME (Binding.name "more")];
    fun declare_const (i, (SOME x, (acc, T))) thy =
          (if is_base andalso i < n then
            (*the base's predicate: the constant unqualified, its definition qualified (3.5)*)
            thy
            |> Sign.declare_const_global ((x, sT --> T), NoSyn)
            |-> (fn c =>
                  qualified #> Global_Theory.add_def (sealed_def x, Logic.mk_equals (c, acc))
                  #>> pair c)
           else thy |> qualified |> define_sealed (x, sT --> T) acc)
          |>> SOME ||> Sign.restore_naming thy
      | declare_const (_, (NONE, _)) thy = (NONE, thy);
    val (consts_defs, thy2) =
      fold_map declare_const (map_index I (named ~~ (accs ~~ (Ts @ [moreT])))) thy1;
    val defs = map_filter (Option.map snd) consts_defs;
    val accs' = map2 (fn SOME (c, _) => K c | NONE => I) consts_defs accs;

    (* the canonical term *)
    val up = (case parent of NONE => [] | SOME p => chain thy2 p);
    val levels = up @ [(name, Ts)];
    val (xss, _) = fold_map (fn (_, Us) => fn i =>
      (map_index (fn (j, U) => Free ("x" ^ string_of_int (i + j), U)) Us, i + length Us)) levels 0;
    val more = Free ("more", moreT);
    val up_layers = map (the_layer thy2 o #1) up;
    val abss = map #abs up_layers @ [abs];
    val whole = whole_of thy2 abss xss more;

    (* accessor theorems *)
    val up_layer = Option.map (fn (_, p) => the_layer thy2 (#owner (the_entry thy2 p))) parent;
    val up_more_conv = the_list (Option.map #more_conv up_layer);
    val convs = map2 (fn acc => fn x =>
        Goal.prove_sorry_global thy2 [] []
          (HOLogic.mk_Trueprop (HOLogic.mk_eq (app thy2 acc whole, x)))
          (fn {context = ctxt, ...} =>
            rewrite_goals_tac ctxt
              (defs @ map meta (up_more_conv @ [abs_inverse] @ @{thms fst_conv snd_conv})) THEN
            resolve_tac ctxt @{thms refl} 1))
      accs' (List.last xss @ [more]);

    (* equality: equal leaves along the chain and equal more give equal values *)
    val r' = Free ("r'", sT);
    val up_accs = maps (map #acc o #leaves) up_layers;
    val prems =
      map (fn acc => HOLogic.mk_Trueprop (HOLogic.mk_eq (app thy2 acc r, app thy2 acc r')))
        (up_accs @ accs');
    val equality =
      Goal.prove_sorry_global thy2 ["r", "r'"] prems (HOLogic.mk_Trueprop (HOLogic.mk_eq (r, r')))
        (fn {context = ctxt, prems} =>
          let
            val (up_prems, own_prems) = chop (length up_accs) prems;
            val own_prems' = map (Raw_Simplifier.rewrite_rule ctxt defs) own_prems;
          in
            (case up_layer of
              NONE => all_tac
            | SOME {equality, ...} =>
                resolve_tac ctxt [equality] 1 THEN
                EVERY (map (fn p => resolve_tac ctxt [p] 1) up_prems)) THEN
            resolve_tac ctxt [@{thm iffD1} OF [Rep_inject]] 1 THEN
            split_tac ctxt (n + 1) 1 THEN
            EVERY (map (fn p => resolve_tac ctxt [p] 1) own_prems')
          end);

    (* surjective: every value is the canonical term of its leaves and more *)
    val applied = map (map (fn acc => app thy2 acc r)) (map (map #acc o #leaves) up_layers @
      [#1 (split_last accs')]);
    val surjective =
      Goal.prove_sorry_global thy2 ["r"] []
        (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (r, whole_of thy2 abss applied (app thy2 (List.last accs') r))))
        (fn {context = ctxt, ...} =>
          (case up_layer of
            NONE => all_tac
          | SOME {surjective = up_surj, ...} => resolve_tac ctxt [@{thm trans} OF [up_surj]] 1) THEN
          rewrite_goals_tac ctxt (defs @ map meta ([Rep_inverse] @ @{thms prod.collapse})) THEN
          resolve_tac ctxt @{thms refl} 1);

    (* truncate: the more slot of this layer replaced by () *)
    val truncT = sT --> Term.typ_subst_atomic [(moreT, HOLogic.unitT)] sT;
    val ((trunc, trunc_def), thy3) = thy2
      |> qualified
      |> define_sealed (Binding.name "truncate", truncT)
          (lambda r (whole_of thy2 abss applied HOLogic.unit))
      ||> Sign.restore_naming thy2;
    val trunc_conv =
      Goal.prove_sorry_global thy3 [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (trunc $ whole, whole_of thy3 abss xss HOLogic.unit)))
        (fn {context = ctxt, ...} =>
          rewrite_goals_tac ctxt
            (trunc_def :: map meta (maps (map #conv o #leaves) up_layers @ convs)) THEN
          resolve_tac ctxt @{thms refl} 1);

    val leaves = map2 (fn ((T, acc), conv) => fn const_def =>
        {name = Option.map (dest_Const_name o fst) const_def, typ = T, acc = acc, conv = conv})
      (Ts ~~ #1 (split_last accs') ~~ #1 (split_last convs)) (#1 (split_last consts_defs));
    val layer: layer =
     {ext = ext_tyco, abs = abs, leaves = leaves, more_conv = List.last convs,
      defs = defs, abs_inverse = abs_inverse, rep_inject = Rep_inject, equality = equality,
      surjective = surjective,
      truncate = trunc, truncate_def = trunc_def, truncate_conv = trunc_conv};

    (* code generation: Abs is the constructor; the accessor theorems and that of truncate are
      code equations *)
    val code_eqns =
      map_filter (fn (SOME _, conv) => SOME conv | _ => NONE) (named ~~ convs) @
      (if forall is_some named then [] else [abs_inverse]) @ [trunc_conv];
  in
    thy3
    |> Code.declare_datatype_global [dest_Const abs]
    |> Code.declare_default_eqns_global (map (rpair true) code_eqns)
    |> put_entry {name = name, args = args, parent = parent, owner = name, layer = SOME layer,
        scheme = sT, more = List.last accs', views = []}
    |> register_layer name
    |> not is_base ? add_laws name
  end;


(* the base concept *)

fun declare_base thy =
  let
    val b = Binding.name "concept";
    val name = Sign.full_name thy b;
    val thy' = add_layer b [] NONE [(b, HOLogic.boolT)] thy;
  in
    thy'
    |> map_data (fn (_, entries, owners, instances) => (SOME name, entries, owners, instances))
    |> add_laws name
    |> add_base_equality
    |> add_equality name
    |> register_printed name
    |> Sign.print_translation [type_tr' (#ext (the_layer thy' name))]
  end;


(* checks of the declaration *)

fun check_parent thy cname (Ts, name) =
  let
    val bname = Long_Name.base_name name;
    val args =
      (case get_entry thy name of
        SOME {args, ...} => args
      | NONE => error ("Unknown parent concept " ^ quote bname ^ " in concept " ^ quote cname));
    val _ = length Ts = length args orelse
      error ("Bad number of type arguments for parent concept " ^ quote bname ^ " in concept " ^
        quote cname ^ ": " ^ string_of_int (length Ts) ^ " given, " ^
        string_of_int (length args) ^ " expected");
    val _ = (Ts ~~ args) |> List.app (fn (T, (a, S)) =>
      if Sign.of_sort thy (T, S) then ()
      else
        error ("Ill-sorted type argument for parent concept " ^ quote bname ^ " in concept " ^
          quote cname ^ ": " ^ Syntax.string_of_typ_global thy T ^ " does not have sort " ^
          Syntax.string_of_sort_global thy S ^ ", as the type parameter " ^ a ^ " of " ^
          quote bname ^ " requires"));
  in () end;

fun check_declaration thy b args parent items =
  let
    val cname = Binding.name_of b;
    val name = Sign.full_name thy b;
    val _ = is_none (get_entry thy name) orelse
      error ("Duplicate definition of concept " ^ quote cname);
    val _ = not (String.isSuffix "_scheme" cname) orelse
      error ("Illegal concept name " ^ quote cname ^
        ": names ending with \"_scheme\" are reserved for the scheme types of concepts");
    val _ = not (Sign.declared_tyname thy (name ^ "_scheme")) orelse
      error ("Illegal concept name " ^ quote cname ^ ": its scheme type needs the name " ^
        quote (cname ^ "_scheme") ^ ", but a type of that name already exists");
    val _ = check_parent thy cname parent;
    val names = items |> map (fn Field (x, _) => x | View {qualifier, ...} => qualifier);
    val _ = names |> List.app (fn x =>
      if not (member (op =) ["more", "super", "truncate"] (Binding.name_of x)) then ()
      else
        error ("Illegal field name " ^ quote (Binding.name_of x) ^ " in concept " ^ quote cname ^
          ": this name is reserved"));
    val dups = duplicates (op =) (map Binding.name_of names);
    val _ = null dups orelse
      error ("Duplicate " ^ plural dups "field" ^ " " ^ commas_quote dups ^ " in concept " ^
        quote cname);
    (*no name inherited along the major chain*)
    val inherited = children thy parent;
    val _ = names |> List.app (fn x =>
      (case AList.lookup (op =) inherited (Binding.name_of x) of
        SOME (_, (c, d)) =>
          error ("The name " ^ quote (Binding.name_of x) ^ " is already bound to " ^
            Proof_Context.extern_const (Proof_Context.init_global thy) c ^ " in concept " ^
            Long_Name.base_name d ^ "\n" ^
            "Concept " ^ cname ^ " inherits this name and cannot define it again\n" ^
            "Use a different name")
      | NONE => ()));
    val _ = items |> List.app
      (fn View {parent = p, ...} => check_parent thy cname p | Field _ => ());
    (*the type variables of the declaration, in order of appearance*)
    val tfrees =
      rev (fold (fn Field (_, T) => Term.add_tfreesT T
          | View {parent = (Ts, _), more, ...} => fold Term.add_tfreesT (Ts @ [more])) items
        (fold Term.add_tfreesT (#1 parent) []));
    val extra = subtract (op =) args tfrees;
    val _ = null extra orelse
      error ("Extra " ^ plural extra "type variable" ^ " " ^ commas (map #1 extra) ^
        " in concept " ^ quote cname ^
        ": every type variable must be a type parameter of the concept");
  in () end;

(*every type parameter occurs in the scheme type: in the major parent's type arguments or in
  the type of a stored leaf; one line for those occurring nowhere, one for those occurring only
  in the parents of views (qualifier, parent) that store no leaf of their type*)
fun check_used cname args (Ts, _) views bleaves =
  let
    val used = fold Term.add_tfreesT (Ts @ map #2 bleaves) [];
    fun occurs_in (_, (Us, _)) a = member (op =) (fold Term.add_tfreesT Us []) a;
    val (nowhere, in_views) =
      List.partition (fn a => not (exists (fn v => occurs_in v a) views))
        (filter_out (member (op =) used) args);
    fun head ps =
      "Unused " ^ plural ps "type parameter" ^ " " ^ commas (map #1 ps) ^ " of concept " ^
        quote cname;
    val nowhere_line =
      if null nowhere then []
      else [head nowhere ^ ": a type parameter must occur in the type of a field"];
    val in_views_line =
      if null in_views then []
      else
        let
          val one = length in_views = 1;
          val qs = views |> filter (fn v => exists (occurs_in v) in_views) |> map #1;
        in
          [head in_views ^ ". Although " ^ commas (map #1 in_views) ^
            (if one then " occurs in " else " occur in ") ^
            (case qs of [_] => "the type of the parent " | _ => "the types of the parents ") ^
            commas_quote qs ^ ", no field actually uses " ^ (if one then "it" else "them")]
        end;
    val lines = nowhere_line @ in_views_line;
  in if null lines then () else error (cat_lines lines) end;


(* declare *)

(*the leaves of the new layer, from the items and per view its stored leaves (index in the
  view's parent, leaf); per view, each stored leaf's index in the parent with its index among the
  leaves of the concept, the next being i*)
fun layer_leaves [] _ _ = ([], [])
  | layer_leaves (Field (x, T) :: items) ss i =
      layer_leaves items ss (i + 1) |>> cons (x, T)
  | layer_leaves (View _ :: items) (s :: ss) i =
      let val n = length s in
        layer_leaves items ss (i + n)
        |> (fn (leaves, anons) =>
          (map (fn (_, {typ, ...}: flat_leaf) => (Binding.empty, typ)) s @ leaves,
           (map #1 s ~~ (i upto i + n - 1)) :: anons))
      end
  | layer_leaves (View _ :: _) [] _ = raise Match;

fun declare {name = b, args, parent, items} thy0 =
  let
    val parent' = the_default ([], base_name thy0) parent;
    val _ = check_declaration thy0 b args parent' items;
    val cname = Binding.name_of b;
    val name = Sign.full_name thy0 b;
    val p_C = (map TFree args, name);

    (* the leaves: the fields, and the leaves of each view not given by its where clauses *)
    val views = map_filter (fn View v => SOME v | Field _ => NONE) items;
    val entriess = views |> map (fn {qualifier, parent = p, more, where_} =>
      let val q = Binding.name_of qualifier
      in resolve_entries thy0 (p, more) (no_field_error thy0 cname [q]) q where_ end);
    val storeds = (views ~~ entriess) |> map (fn ({parent = p, more, ...}, entries) =>
      map_index I (node_leaves thy0 (p, more))
      |> filter_out (member (op =) (maps (map #1 o given_leaves thy0 o #3) entries) o #1));
    val (bleaves, anons) = layer_leaves items storeds (length (flat_leaves thy0 parent'));
    val _ = check_used cname args parent'
      (views |> map (fn {qualifier, parent = (Ts, r), more, ...} =>
        (Binding.name_of qualifier, (Ts @ [more], r)))) bleaves;

    (* the type: a new layer, or the parent's *)
    val thy1 =
      if null bleaves then
        let
          val {owner, more, ...} = the_entry thy0 (#2 parent');
          val zeta = more_var (map #1 args);
          val sT = scheme_type thy0 parent' (TFree zeta);
        in
          thy0
          |> abbrev_types b args zeta sT
          |> put_entry {name = name, args = args, parent = SOME parent', owner = owner,
              layer = NONE, scheme = sT, more = Const (dest_Const_name more, sT --> TFree zeta),
              views = []}
        end
      else add_layer b args (SOME parent') bleaves thy0;

    (* the context of the right-hand sides: S, every field and every view is a variable *)
    val sT = #scheme (the_entry thy1 name);
    val leaves_C = flat_leaves thy1 p_C;
    val inherited_views =
      children thy1 parent' |> map_filter (fn (x, (View_Child {const, parent, more, ...}, _)) =>
        SOME (x, const, scheme_type thy1 parent more) | _ => NONE);
    val fields =
      leaves_C |> map_index I |> map_filter (fn (i, {name = SOME c, typ, ...}) =>
        SOME (Long_Name.base_name c, typ, i) | _ => NONE);
    val ctxt0 = Proof_Context.init_global thy1 |> fold (Variable.declare_typ o TFree) args;
    val ([s_name], ctxt1) = Proof_Context.add_fixes [(Binding.name "\<S>", SOME sT, NoSyn)] ctxt0;
    val S = Free (s_name, sT);
    val (field_names, ctxt2) =
      Proof_Context.add_fixes (map (fn (x, T, _) => (Binding.name x, SOME T, NoSyn)) fields) ctxt1;
    val (inherited_names, ctxt3) = Proof_Context.add_fixes
      (map (fn (x, _, T) => (Binding.name x, SOME T, NoSyn)) inherited_views) ctxt2;
    val (view_names, ctxt) = Proof_Context.add_fixes
      (views |> map (fn {qualifier, parent = p, more, ...} =>
        (qualifier, SOME (scheme_type thy1 p more), NoSyn))) ctxt3;
    val base_subst =
      (s_name, S) ::
      map2 (fn x => fn (_, _, i) => (x, read_leaf thy1 p_C i S)) field_names fields @
      map2 (fn x => fn (_, c, _) => (x, app thy1 c S)) inherited_names inherited_views;

    fun read_entry idx qname view_consts (entry as (path, _, given)) =
      let
        val pos = #2 (List.last path);
        val {parent = p_R, more, ...} = nth views idx;
        val t = read_given thy1 ctxt (p_R, more) qname entry;
        val field = quote (qname ^ "." ^ implode_path (map #1 path)) ^ Position.here pos;
        val _ = Term.add_frees t [] |> List.app (fn (x, _) =>
          (case find_index (fn v => v = x) view_names of
            ~1 =>
              if AList.defined (op =) base_subst x then () else undefined_constant field x
          | k =>
              if k < idx then ()
              else if k = idx then
                error ("The assignment of the field " ^ field ^ " uses " ^ quote qname ^
                  " itself, which is a circular reference")
              else
                let val x' = Binding.name_of (#qualifier (nth views k)) in
                  error ("The assignment of the field " ^ field ^ " uses " ^ quote x' ^
                    ", which is not defined yet. Move " ^ quote x' ^ " before " ^ quote qname)
                end));
        val _ = check_determined ctxt sT field t;
        val subst =
          base_subst @ map2 (fn x => fn c => (x, c $ S)) (take idx view_names) view_consts;
        val t' = t |> Term.map_aterms (fn a as Free (x, _) =>
          the_default a (AList.lookup (op =) subst x) | a => a);
      in given_values thy1 given t' end;

    fun define_view ((idx, {qualifier, parent = p_R, more = more_R, ...}), (entries, anon))
        (view_consts, thy) =
      let
        val qname = Binding.name_of qualifier;
        val given = maps (read_entry idx qname view_consts) entries;
        (*the slots of the view: the leaves of its parent, and its more unless that is ()*)
        val slots_R = node_leaves thy (p_R, more_R);
        val values =
          map_index (fn (j, _) =>
            (case AList.lookup (op =) given j of
              SOME t => t
            | NONE => app thy (#acc (nth leaves_C (the (AList.lookup (op =) anon j)))) S))
          slots_R;
        val (leaf_values, more_value) =
          if more_R = HOLogic.unitT then (values, HOLogic.unit) else split_last values;
        val value = mk_value thy p_R \<^Const>\<open>True\<close> leaf_values more_value;
        val ((c, def), thy') = thy
          |> Sign.qualified_path true b
          |> define_sealed (qualifier, sT --> scheme_type thy p_R more_R) (lambda S value)
          ||> Sign.restore_naming thy;
        val (concept_eq, code_eq) =
          prove_definitional thy' def [s_name] (c $ S) \<^Const>\<open>True\<close> value;

        (*the leaves of the concept that read_leaf can read, with their reads*)
        val held =
          major_chain thy' p_C |> maps (fn (_, d) =>
            maps (map_filter (fn Leaf i => SOME i | Given _ => NONE) o #slots)
              (#views (the_entry thy' d)));
        val candidates =
          map_index I leaves_C |> map_filter (fn (i, {name, ...}) =>
            if is_some name orelse member (op =) held i
            then SOME (read_leaf thy' p_C i S, Leaf i) else NONE);
        (*each leaf of the parent: the leaf of the concept it reads, or given*)
        fun slot_of j =
          (case AList.lookup (op =) given j of
            SOME t => the_default (Given (name, t)) (AList.lookup (op aconv) candidates t)
          | NONE => Leaf (the (AList.lookup (op =) anon j)));
        val view: view_entry =
         {name = dest_Const_name c, qualifier = qname, const = c, parent = p_R, more = more_R,
          slots = map_index (slot_of o #1) slots_R, S = S, values = values, def = def,
          concept_eq = concept_eq};
      in
        (view_consts @ [c],
          thy'
          |> Code.declare_default_eqns_global [(code_eq, true)]
          |> add_view view name
          |> register (dest_Const_name c) (View_Const name)
          |> add_derived_congs c def [s_name])
      end;

    val (_, thy2) =
      fold define_view (map_index I views ~~ (entriess ~~ anons)) ([], thy1);
    val thy3 = thy2 |> add_split name |> add_equality name |> register_printed name;
  in (the_info thy3 name, thy3) end;


(** instances **)

(* families *)

type covering = {layer: string, member: string, exact: bool};

(*the member providing a layer of a family; exact: its type ends at that layer*)
fun covering thy family layer : covering option =
  Symtab.lookup (providers thy family) layer
  |> Option.map (fn {member, ...} =>
      let val {concept = (_, c), ...} = the (get_instance_entry thy member)
      in {layer = layer, member = member, exact = #owner (the_entry thy c) = layer} end);

(*the layers of the type of a concept, from the last toward the base, without the base's*)
fun layers_of thy p = rev (map #1 (tl (chain thy p)));

(*the layer owning the type of a concept, with the member of the family providing it*)
fun own_layer thy {family, concept} =
  let val layer = #owner (the_entry thy concept) in (layer, covering thy family layer) end;

(*the first layer of the type of a concept, from the last toward the base, that the family
  provides*)
fun covered_layer thy {family, concept} =
  get_first (covering thy family)
    (layers_of thy (map TFree (#args (the_entry thy concept)), concept));


(* keys *)

(*the key of a structure term: that of its head below the truncations, the family for a member
  of a family*)
fun key_of thy t =
  (case dest_truncation thy t of
    SOME (_, u) => key_of thy u
  | NONE =>
      (case Term.head_of t of
        Const (c, _) =>
          (case get_instance_entry thy c of SOME {family = SOME f, ...} => SOME f | _ => SOME c)
      | _ => NONE));

(*the keys linked to a key, through any number of links*)
fun linked_keys thy key =
  let
    val links = Links.get thy;
    fun reach k seen =
      if member (op =) seen k then seen else fold reach (Symtab.lookup_list links k) (k :: seen);
  in remove (op =) key (reach key []) end;

(*the position, from 0, of the parameter that "where super = ..." names*)
fun super_param thy c =
  (case get_instance_entry thy c of
    SOME {params, source = SOME {kind = Super, term, ...}, ...} =>
      (case find_index (fn x => x aconv term) params of ~1 => NONE | i => SOME i)
  | _ => NONE);


(* implications *)

(*concept (c ?xs) ==> concept u for the instance c: u its source, or one of ?xs*)
fun add_implication c th thy =
  let
    val {name, const, concept, params, values, more, wholes, constraint, def, concept_eq, family,
      source, implications} = the (get_instance_entry thy c);
    val structure_of = #2 o dest_comb o HOLogic.dest_Trueprop;
    val (prem, concl) = Logic.dest_implies (Thm.prop_of th);
    val i = find_index (fn x => x aconv structure_of concl) (#2 (strip_comb (structure_of prem)));
    val to_source =
      i < 0 orelse (case source of SOME {term, ...} => nth params i aconv term | NONE => false);
    val source' =
      if not to_source then source
      else
        source |> Option.map (fn {kind, layer, term, fields, ...} =>
          {kind = kind, layer = layer, term = term, fields = fields, forward = SOME th});
  in
    thy |> put_instance
     {name = name, const = const, concept = concept, params = params, values = values,
      more = more, wholes = wholes, constraint = constraint, def = def, concept_eq = concept_eq,
      family = family, source = source',
      implications = if i < 0 then implications else Inttab.update (i, th) implications}
  end;


(* define *)

(*the constant x :: params => D, its value built from the where clauses; the layers that its
  source has are taken from the source, whose values must agree with the given ones.  The
  source is the t of "where super = t", else the member of the family providing the nearest
  layer of D.  Without define, which the caller passes only when a member of the family owns
  the layer of D and no super is given, no constant is made: the given values are checked
  against that member, which is returned*)
fun define_instance ctxt
    {family, name = b, define, concept = p_D, params, where_, constraint} thy =
  let
    val xname = Binding.long_name_of b;
    val dname = Long_Name.base_name (#2 p_D);
    val leaves_D = flat_leaves thy p_D;
    val (more_clauses, clauses) =
      List.partition (fn ([("more", _)], _) => true | _ => false) where_;
    val entries =
      resolve_entries thy (p_D, HOLogic.unitT) (no_field_error thy dname []) xname clauses;
    val param_names = map (#1 o dest_Free) params;
    val paramTs = map fastype_of params;
    fun field_of path = quote (implode_path (map #1 path)) ^ Position.here (#2 (List.last path));
    fun check_params field t =
      Term.add_frees t [] |> List.app (fn (x, _) =>
        if member (op =) param_names x then () else undefined_constant field x);

    (* more: given by a where clause, else () *)
    (*the type variables of the constant are declared: type inference gives a type left open
      another name*)
    val ctxt = Variable.declare_typ (paramTs ---> unit_type thy p_D) ctxt;
    val more =
      (case more_clauses of
        [] => HOLogic.unit
      | [(path, rhs)] =>
          let val t = Syntax.read_term ctxt rhs
          in check_params (field_of path) t; t end
      | _ :: (path, _) :: _ =>
          error ("The field more of " ^ xname ^ " is specified twice" ^
            Position.here (#2 (List.last path))));
    val T = paramTs ---> scheme_type thy p_D (fastype_of more);
    val ctxt = Variable.declare_typ T ctxt;
    val _ = more_clauses |> List.app (fn (path, _) => check_determined ctxt T (field_of path) more);

    (*a right-hand side uses only the parameters and determines its types*)
    fun read_entry (entry as (path, _, _)) =
      let
        val t = read_given thy ctxt (p_D, HOLogic.unitT) xname entry;
        val field = field_of path;
        val _ = check_params field t;
        val _ = check_determined ctxt T field t;
      in (entry, t) end;
    val read = map read_entry entries;
    val given = maps (fn ((_, _, g), t) => given_values thy g t) read;

    (* the source, with the values of the leaves taken from a member of the family *)
    fun part layer p =
      unit_type thy (the (find_first (fn (_, c) => c = layer) (major_chain thy p)));
    fun member_at layer ({member, shown, ...}: provider) =
      let
        val src as {const, concept = p_A, params = params_A, ...} =
          the (get_instance_entry thy member);
        val print_typ = quote o Syntax.string_of_typ ctxt;
        (*what is compared: the two members as functions of their parameters, cut down to the
          layer*)
        val T_A = map fastype_of params_A ---> part layer p_A;
        val T_D = paramTs ---> part layer p_D;
        fun type_error () =
          let
            val l = Long_Name.base_name layer;
            (*a member with a wider type of its own is named by its part*)
            val shown' = if fastype_of const = T_A then shown else "the " ^ l ^ " part of " ^ shown;
          in
            error (cat_lines
             ["Cannot define " ^ xname ^ Position.here (Binding.pos_of b) ^ ": its " ^ l ^
                " part must have the type of " ^ shown' ^ ", which the family " ^
                Long_Name.base_name (the family) ^ " already has",
              "  " ^ shown' ^ " :: " ^ print_typ T_A,
              "  the " ^ l ^ " part of " ^ xname ^ " :: " ^ print_typ T_D,
              "Check your type declarations"])
          end;
        val tyenv =
          Sign.typ_match thy (Logic.varifyT_global T_A, T_D) Vartab.empty
          handle Type.TYPE_MATCH => type_error ();
        val m = Envir.subst_term_types tyenv o Logic.varify_types_global;
        val t = list_comb (m const, params);
        val values = map (instance_subst m src params) (take (leaf_count thy layer) (#values src));
      in (src, (Family, layer, t), map_index I values) end;
    val super =
      get_first (fn ((path, _, Given_Node (p', _, _, _)), t) =>
          if forall (fn (seg, _) => seg = "super") path
          then SOME (Super, #owner (the_entry thy (#2 p')), t) else NONE
        | _ => NONE) read;
    val provided =
      (case (super, family) of
        (NONE, SOME f) =>
          layers_of thy p_D |> get_first (fn layer =>
            Option.map (member_at layer) (Symtab.lookup (providers thy f) layer))
      | _ => NONE);
    val inherited = (case provided of SOME (_, _, values) => values | NONE => []);
    (*values agree when the selector Simpset rewrites them to the same term*)
    val normal =
      Thm.term_of o Thm.rhs_of o Simplifier.rewrite (put_selector_simpset ctxt) o Thm.cterm_of ctxt;
    val _ = given |> List.app (fn (j, t) =>
      (case AList.lookup (op =) inherited j of
        SOME u =>
          if t aconv u orelse normal t aconv normal u then ()
          else
            error ("The field " ^ implode_path (leaf_path thy p_D j) ^ " of " ^ xname ^
              " has been defined as " ^ Syntax.string_of_term ctxt u ^
              ", but here you specified a different value `" ^ Syntax.string_of_term ctxt t ^ "`")
      | NONE => ()));
    (*the more of a view needs no value where its type is unit*)
    val units =
      map_index I leaves_D |> map_filter (fn (j, {name, typ, ...}) =>
        if is_none name andalso typ = HOLogic.unitT andalso
          List.last (leaf_path thy p_D j) = "more"
        then SOME (j, HOLogic.unit) else NONE);
    (*the layers of the source hold the source's values as they are written there*)
    val value_of = AList.lookup (op =) (inherited @ given @ units);
    val missing = filter_out (is_some o value_of o #1) (map_index I leaves_D);
    val _ = null missing orelse
      let
        val one = length missing = 1;
        fun line (j, {typ, ...}: flat_leaf) =
          "  " ^ implode_path (leaf_path thy p_D j) ^ " :: " ^
            quote (Syntax.string_of_typ ctxt typ);
      in
        error ((if one then "This field of " else "These fields of ") ^ xname ^
          Position.here (Binding.pos_of b) ^ (if one then " is" else " are") ^
          " not specified:\n" ^ cat_lines (map line missing))
      end;
    val values = map_index (the o value_of o #1) leaves_D;
    (*the clauses whose path ends at a view*)
    val wholes =
      read |> map_filter (fn ((path, _, Given_Node (_, _, _, views)), t) =>
          if #1 (List.last path) = "super" then NONE else SOME (views, t)
        | _ => NONE);

    (* the constant and its sealed definition *)
    fun defined () =
      let
        val value = mk_value thy p_D constraint values more;
        val ((c, def), thy1) = define_sealed (b, T) (fold_rev lambda params value) thy;
        val cname = dest_Const_name c;
        val lhs = list_comb (c, params);
        val (concept_eq, code_eq) =
          prove_definitional thy1 def param_names lhs constraint value;
        val base_more = app thy1 (#more (the_entry thy1 (base_name thy1)));
        val source =
          (case (super, provided) of (NONE, SOME (_, s, _)) => SOME s | _ => super)
          |> Option.map (fn (kind, layer, t) =>
            let val truncate = app thy1 (#truncate (the_layer thy1 layer)) in
              {kind = kind, layer = layer, term = t,
               fields =
                prove_unfold thy1 [def] param_names (base_more (truncate lhs))
                  (base_more (truncate t)),
               forward = NONE}
            end);
        val instance: instance_entry =
         {name = cname, const = c, concept = p_D, params = params, values = values, more = more,
          wholes = wholes, constraint = constraint, def = def, concept_eq = concept_eq,
          family = family, source = source, implications = Inttab.empty};
        (*this member provides the layers of its type that nothing provides yet*)
        val provider: provider =
         {member = cname, shown = xname, theory = Context.theory_base_name thy,
          pos = Binding.pos_of b, layers = layers_of thy p_D};
        fun provide f =
          Families.map (Symtab.map_default (f, Symtab.empty)
            (fold (fn layer => Symtab.default (layer, provider)) (#layers provider)));
        val key = the_default cname family;
        val link =
          (case source of
            SOME {kind = Super, term, ...} =>
              (case key_of thy1 term of
                SOME k =>
                  if k = key then I
                  else
                    Links.map
                      (Symtab.insert_list (op =) (key, k) #> Symtab.insert_list (op =) (k, key))
              | NONE => I)
          | _ => I);
      in
        (instance_of instance,
          thy1
          (*a global instance without parameters is computable*)
          |> null params ? Code.declare_default_eqns_global [(code_eq, true)]
          |> put_instance instance
          |> add_derived_congs c def param_names
          |> (case family of SOME f => provide f | NONE => I)
          |> link)
      end;
  in
    if define then defined ()
    else let val (src, _, _) = the provided in (instance_of src, thy) end
  end;

end;
