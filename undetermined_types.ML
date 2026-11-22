(*  Title:      undetermined_types.ML

Where a term needs type annotations.  Type inference gives a fresh type variable to every type
that the term and its context do not determine.  A package that turns the term into a
definition can tell them apart: they are the type variables not in the type of the constant
being defined, and the kernel rejects the definition for them.  This module names the terms
whose annotation determines these types, as the user wrote them.
*)

signature UNDETERMINED_TYPES =
sig
  val to_annotate: (string * sort) list -> term -> term list
  val message: Proof.context -> term list -> string
end;

structure Undetermined_Types: UNDETERMINED_TYPES =
struct

(*the terms of t to annotate, in order of appearance: one for each type variable of t not among
  the determined ones, that of the smallest type having it, the first on ties.  The candidates
  are the constants and variables of t, a number literal as a whole, and the bound variables as
  free variables; a bound variable named by the parser is taken only when nothing else has the
  type variable*)
fun to_annotate determined t =
  let
    fun open_vars u = subtract (op =) determined (Term.add_tfrees u []);
    fun add u = if null (open_vars u) then I else insert (op aconv) u;
    fun add_candidates u =
      if can HOLogic.dest_number u then add u
      else
        (case u of
          Abs (x, T, b) => add (Free (x, T)) #> add_candidates b
        | v $ w => add_candidates v #> add_candidates w
        | Bound _ => I
        | _ => add u);
    val candidates = rev (add_candidates t []);
    fun rank u =
      ((case u of Free (x, _) => Name.is_internal x | _ => false), Term.size_of_typ (fastype_of u));
    fun better (u, v) = if is_less (prod_ord bool_ord int_ord (rank v, rank u)) then v else u;
    fun term_for a = foldl1 better (filter (fn u => member (op =) (open_vars u) a) candidates);
    val chosen = map term_for (fold (union (op =) o open_vars) candidates []);
  in filter (member (op aconv) chosen) candidates end;

(*what to say about a term with these terms to annotate, each printed as the user wrote it*)
fun message ctxt terms =
  let
    (*a number literal without the type that the printer would add*)
    val ctxt' = Config.put Printer.show_type_emphasis false ctxt;
    val print = quote o Syntax.string_of_term ctxt';
  in
    (case terms of
      [u] => "needs a type annotation on the term " ^ print u
    | _ => "needs type annotations on the terms " ^ commas (map print terms))
  end;

end;
