(*  Title:      concept_search.ML

The search of concept_fact.

The kernel knows goals only by what a problem tells of them: the key of a goal as it is solved,
and the steps that apply to it.  A step is a rule on the goal: a premise of it is a goal again, at
the distance of the goal or a leap further, or a condition that is left to the user.  The
effective distance of a solution adds, for every step that leaves conditions, the distance of its
goal and its leap.  The search takes the solutions of least effective distance: the first one
found where that is 0, else all of them, as far as the number of solutions allows; the solutions
of one goal are alternatives.

Branches are taken from a queue by effective distance, then by the number of steps that leave
conditions, then by the number of steps, then by age.  A table has every goal at its distance:
being solved, with the branches that wait for it, or solved, with its first solution and the
solutions recorded after it that tie with it.  A goal solved without conditions serves at every
distance.

A premise may stand under a wrapper: parameters and hypotheses around its goal.  The search
solves the goal without looking at them; what the solution leaves stands under the wrapper.

What a problem tells of a goal or makes of a condition may take a search of its own: the kernel
tells it the situation, for that search to go on from.  The key of a goal is asked for when a
branch takes the goal up, and the branch may have to wait for a goal under way on it.
*)

signature CONCEPT_SEARCH_KERNEL =
sig
  datatype ('a, 'c) premise = Subgoal of 'a | Condition of 'c
  type ('g, 'r, 'c) step =
   {rule: 'r, premises: ('g * bool, 'c) premise list, leap: int, user: bool}
  type ('g, 'w, 's) reading =
   {wrapper: 'g -> 'w option, trivial: 's -> bool, same: 's * 's -> bool,
    same_wrapper: 'w * 'w -> bool}
  datatype ('g, 'r, 's) derivation =
    Derivation of
     {goal: 'g,
      solutions: {rule: 'r, premises: (('g, 'r, 's) derivation, 's) premise list} list}
  type ('g, 'r, 's) solution =
   {rule: 'r, premises: (('g, 'r, 's) derivation, 's) premise list}
  type 'g situation =
   {dist: int, steps: int, under_way: ('g * (int * int)) list}
  exception STOP
  exception WAIT of int * int
  exception ASIDE
  type ('g, 'w, 'r, 'c, 's) problem =
   {key: 'g situation -> 'g -> int, steps: 'g -> ('g, 'r, 'c) step list,
    user_rule: unit -> unit, solved: 'g -> (unit -> ('g, 'r, 's) solution list) -> unit,
    simplify: 'g situation -> 'c -> 's, as_written: 'c -> 's,
    reading: ('g, 'w, 's) reading}
  type limits =
   {max_search_distance: int, max_leaps: int, max_solution_number: int, unconditional: bool}
  datatype ('w, 's) literal =
      Cond of 's
    | Or of ('w, 's) literal list list
    | Under of 'w * ('w, 's) literal
  val count: ('w, 's) literal list -> int
  val conditions: ('g, 'w, 's) reading -> ('g, 'r, 's) derivation -> ('w, 's) literal list
  datatype failure = No_Plan | User_Limit
  datatype ('g, 'w, 'r, 's) result =
      Found of
       {derivation: ('g, 'r, 's) derivation, conditions: ('w, 's) literal list, distance: int,
        count: int, cut_short: bool}
    | Failed of failure
  val search: ('g, 'w, 'r, 'c, 's) problem -> limits -> {goal: 'g, dist: int, steps: int} ->
    ('g, 'w, 'r, 's) result
end;

structure Concept_Search_Kernel: CONCEPT_SEARCH_KERNEL =
struct

(** problems **)

(*a premise of a rule: a goal again, or a condition that the rule leaves*)
datatype ('a, 'c) premise = Subgoal of 'a | Condition of 'c;

fun map_premise f _ (Subgoal a) = Subgoal (f a)
  | map_premise _ g (Condition c) = Condition (g c);

(*a rule on a goal.  premises: in their order, a goal with whether it stays at the distance of
  the goal of the rule; user: a user rule: its step counts for the limit on user rules where it
  leaves a condition*)
type ('g, 'r, 'c) step =
 {rule: 'r, premises: ('g * bool, 'c) premise list, leap: int, user: bool};

(*how the conditions that a derivation leaves are read.  wrapper: the one under which a goal
  stands as a premise; trivial: a condition that holds as it stands; same: two conditions that
  say the same; a condition says the same wherever it stands, under a wrapper or not*)
type ('g, 'w, 's) reading =
 {wrapper: 'g -> 'w option, trivial: 's -> bool, same: 's * 's -> bool,
  same_wrapper: 'w * 'w -> bool};

(*what a search finds of a goal: its solutions, alternatives of one another, each a rule with
  what was found of its goals and with its conditions*)
datatype ('g, 'r, 's) derivation =
  Derivation of
   {goal: 'g,
    solutions: {rule: 'r, premises: (('g, 'r, 's) derivation, 's) premise list} list};

type ('g, 'r, 's) solution = {rule: 'r, premises: (('g, 'r, 's) derivation, 's) premise list};

(*where the search stands when it asks for the key of a goal, or for a condition as it is given
  to the user.  dist, steps: of that goal, or of the goal whose solution leaves the condition;
  under_way: the goals that are being solved on the branch of the goal, each with its entry*)
type 'g situation =
 {dist: int, steps: int, under_way: ('g * (int * int)) list};

(*what the functions of a problem may raise.  STOP: the search ends with what it has; WAIT, from
  key only: the goal cannot be told before the entry is solved, which is one of under_way; ASIDE,
  from key only: the goal cannot be told in this search, and the branch is left aside*)
exception STOP;
exception WAIT of int * int;
exception ASIDE;

(*key: goals of one key are one goal to the table; steps: in the order in which they are tried;
  user_rule: called for every step of a user rule that a branch takes and that leaves a
  condition; solved: called when a goal is first solved without conditions, with what gives its
  solutions then and later;
  simplify: of a condition as a rule leaves it, the condition as it is given to the user;
  as_written: the same without any work*)
type ('g, 'w, 'r, 'c, 's) problem =
 {key: 'g situation -> 'g -> int, steps: 'g -> ('g, 'r, 'c) step list,
  user_rule: unit -> unit, solved: 'g -> (unit -> ('g, 'r, 's) solution list) -> unit,
  simplify: 'g situation -> 'c -> 's, as_written: 'c -> 's,
  reading: ('g, 'w, 's) reading};

(*max_search_distance: no step with premises on a goal whose distance and number of steps add
  up to it; max_leaps: no branch of this effective distance; max_solution_number: of the
  solutions of the result, as its conditions show them; unconditional: no step that leaves
  conditions*)
type limits =
 {max_search_distance: int, max_leaps: int, max_solution_number: int, unconditional: bool};



(** conditions **)

(*A conjunction is a list of literals, none twice; the empty one is true.  A disjunction has
  two branches or more, each a conjunction.  Under: a literal under a wrapper; a conjunction
  under a wrapper is its literals, each under the wrapper*)
datatype ('w, 's) literal =
    Cond of 's
  | Or of ('w, 's) literal list list
  | Under of 'w * ('w, 's) literal;

fun same_literal ({same, same_wrapper, ...}: ('g, 'w, 's) reading) =
  let
    fun eq (Cond a, Cond b) = same (a, b)
      | eq (Or bs, Or cs) = eq_set (eq_set eq) (bs, cs)
      | eq (Under (w, a), Under (w', b)) = same_wrapper (w, w') andalso eq (a, b)
      | eq _ = false;
  in eq end;

(*xs, then what ys has more*)
fun join eq xs ys = xs @ subtract eq xs (distinct eq ys);

(*the branches that have no other branch as a part: A or (A and B) is A*)
fun absorb eq conjs =
  conjs |> filter_out (fn b =>
    exists (fn c => subset eq (c, b) andalso not (subset eq (b, c))) conjs);

(*A conjunction and a disjunction made simpler, by steps that keep what they say, until no step
  applies; ctx and outer: the literals that hold around them.  A literal that holds around is
  dropped; under a wrapper, what holds around the wrapper holds, and what holds around it under
  the same wrapper.  A branch with another branch as a part is dropped, so a true branch leaves
  the disjunction true; then a disjunction that is a branch becomes its branches; what all
  branches have is taken out of the disjunction*)
fun clean_conj (reading as {same_wrapper, ...}: ('g, 'w, 's) reading) ctx lits =
  let
    val eq = same_literal reading;
    fun inside w =
      map_filter (fn Under (w', l) => if same_wrapper (w, w') then SOME l else NONE | _ => NONE);
    fun normal lits = subtract eq ctx (distinct eq lits);
    fun pass [] lits changed = (lits, changed)
      | pass (d :: todo) lits changed =
          if member eq lits d then
            let
              val around = join eq ctx (remove eq d lits);
              val replacement =
                (case d of
                  Or branches => clean_or reading around branches
                | Under (w, l) =>
                    map (fn l' => Under (w, l'))
                      (clean_conj reading (join eq around (inside w around)) [l])
                | Cond _ => [d]);
            in
              if eq_set eq (replacement, [d]) then pass todo lits changed
              else
                pass todo (normal (maps (fn l => if eq (l, d) then replacement else [l]) lits))
                  true
            end
          else pass todo lits changed;
    fun loop lits =
      (case pass (filter_out (fn Cond _ => true | _ => false) lits) lits false of
        (lits', true) => loop lits'
      | (lits', false) => lits');
  in loop (normal lits) end
and clean_or reading outer branches =
  let
    val eq = same_literal reading;
    val eq_conj = eq_set eq;
    fun round common bs =
      (case
        map (clean_conj reading (join eq outer common)) bs
        |> distinct eq_conj |> absorb eq
        |> maps (fn [Or inner] => inner | b => [b]) |> distinct eq_conj |> absorb eq
       of
        [b] => join eq common b
      | bs' =>
          let
            val shared = filter (fn l => forall (fn b => member eq b l) bs') (hd bs');
            val common' = join eq common shared;
            val bs'' = map (subtract eq shared) bs';
          in if eq_set eq_conj (bs'', bs) then common' @ [Or bs''] else round common' bs'' end);
  in round [] (distinct eq_conj branches) end;

fun clean reading = clean_conj reading [];

(*the solutions that a conjunction shows: one, and one more for every further branch of a
  disjunction, wherever it stands*)
fun count conj =
  let
    fun further (Cond _) = 0
      | further (Or bs) = length bs - 1 + fold (fold (Integer.add o further)) bs 0
      | further (Under (_, l)) = further l;
  in 1 + fold (Integer.add o further) conj 0 end;

(*what the solutions of a goal leave: each what its premises leave in their order, a goal by
  its own solutions, a condition itself; alternatives of one another; under the wrapper of the
  goal*)
fun leave (reading as {wrapper, trivial, ...}: ('g, 'w, 's) reading) goal sols =
  let
    val eq = same_literal reading;
    fun left (Subgoal conj) = conj
      | left (Condition c) = if trivial c then [] else [Cond c];
    fun solution premises = fold (fn premise => fn conj => join eq conj (left premise)) premises [];
    val conj = (case map solution sols of [conj] => conj | conjs => [Or conjs]);
  in
    (case wrapper goal of SOME w => map (fn l => Under (w, l)) conj | NONE => conj)
  end;



(** the search **)

(*the conditions that a derivation leaves, made simpler*)
fun conditions (reading: ('g, 'w, 's) reading) derivation =
  let
    fun left (Derivation {goal, solutions}) =
      leave reading goal (solutions |> map (fn {premises, ...} =>
        map (map_premise left I) premises));
  in clean reading (left derivation) end;

datatype failure = No_Plan | User_Limit;

(*cut_short: STOP ended the search after its first solution*)
datatype ('g, 'w, 'r, 's) result =
    Found of
     {derivation: ('g, 'r, 's) derivation, conditions: ('w, 's) literal list, distance: int,
      count: int, cut_short: bool}
  | Failed of failure;

(*the key of a goal with its distance*)
structure Keytab = Table(type key = int * int val ord = prod_ord int_ord int_ord);

(*the branches waiting, by effective distance, steps that leave conditions, steps, age*)
structure Queue = Table(type key = int list val ord = dict_ord int_ord);

(*what a branch has to do next: a goal; or the end of the solution of a goal, with the three
  numbers of the branch when it began*)
datatype 'g item =
    Todo of {goal: 'g, dist: int, steps: int}
  | Done of {key: int * int, goal: 'g, eff: int, ncond: int, nrules: int};

(*a step under way on a goal at dist after steps, with its goals closed so far, the latest
  first: each with the entry that closes it*)
type ('g, 'r, 'c) frame =
 {rule: 'r, premises: ('g * bool, 'c) premise list, closed: ('g * (int * int)) list,
  dist: int, steps: int};

(*the three numbers of a branch: its effective distance, its steps that leave conditions, its
  steps; frames: the innermost first*)
type ('g, 'r, 'c) branch =
 {eff: int, ncond: int, nrules: int, items: 'g item list, frames: ('g, 'r, 'c) frame list};

(*a condition of a solution of a goal at dist after steps: as its rule leaves it, and as it
  is given to the user once that has been made*)
type ('c, 's) cell = {raw: 'c, dist: int, steps: int, simplified: 's option Unsynchronized.ref};

(*a solution of a goal: a step with what closes each of its goals*)
type ('g, 'r, 'c, 's) alt =
 {rule: 'r, premises: ('g * (int * int), ('c, 's) cell) premise list};

(*solved: the three numbers of the first solution; alts: the first solution, then the recorded
  ones; waiting: the latest first*)
type ('g, 'r, 'c, 's) entry =
 {solved: (int * int * int) option, alts: ('g, 'r, 'c, 's) alt list,
  waiting: ('g, 'r, 'c) branch list};

(*the search for a top goal of the key top_id*)
fun search_told (problem: ('g, 'w, 'r, 'c, 's) problem) (limits: limits)
    {goal = top, dist = top_dist, steps = top_steps} top_id =
  let
    val {key = key_of, steps = steps_of, user_rule, solved = on_solved, simplify, as_written,
      reading} = problem;
    val {max_search_distance, max_leaps, max_solution_number, unconditional} = limits;
    val top_key = (top_id, top_dist);


    (* the queue *)

    val queue = Unsynchronized.ref (Queue.empty: ('g, 'r, 'c) branch Queue.table);
    val age = Unsynchronized.ref 0;
    fun push (b as {eff, ncond, nrules, ...}: ('g, 'r, 'c) branch) =
      Unsynchronized.change queue
        (Queue.update ([eff, ncond, nrules, Unsynchronized.inc age], b));


    (* the table *)

    val table = Unsynchronized.ref (Keytab.empty: ('g, 'r, 'c, 's) entry Keytab.table);
    (*the goals solved without conditions, each with the entry that solved it first: that entry
      serves the goal at every distance.  Nothing below it leaves a condition, and no tie is
      recorded there: a premise closed by it adds nothing to the conditions and nothing to
      judge*)
    val unconditional_keys = Unsynchronized.ref (Inttab.empty: (int * int) Inttab.table);
    fun the_entry key = the (Keytab.lookup (! table) key);
    fun solved key = is_some (#solved (the_entry key));
    fun map_entry key f = Unsynchronized.change table (Keytab.map_entry key f);
    fun wait key b =
      map_entry key (fn {solved, alts, waiting} =>
        {solved = solved, alts = alts, waiting = b :: waiting});
    fun alt_of ({rule, premises, closed, dist, steps}: ('g, 'r, 'c) frame) =
      let
        fun fill (Subgoal _ :: premises) (closing :: closed) =
              Subgoal closing :: fill premises closed
          | fill (Condition c :: premises) closed =
              Condition
               {raw = c, dist = dist, steps = steps, simplified = Unsynchronized.ref NONE} ::
                fill premises closed
          | fill _ _ = [];
      in {rule = rule, premises = fill premises (rev closed)}: ('g, 'r, 'c, 's) alt end;
    fun close closing (({rule, premises, closed, dist, steps}: ('g, 'r, 'c) frame) :: frames) =
          {rule = rule, premises = premises, closed = closing :: closed, dist = dist,
           steps = steps} :: frames
      | close _ [] = [];
    (*the goals that are being solved on a branch that still has these items to do, and are
      solved at no distance: one solved without conditions serves here too*)
    fun under_way items =
      items |> map_filter (fn Done {key, goal, ...} =>
          if solved key orelse Inttab.defined (! unconditional_keys) (#1 key) then NONE
          else SOME (goal, key)
        | Todo _ => NONE);


    (* what solutions make of a goal *)

    fun admitted_at admitted key = the_default [0] (Keytab.lookup admitted key);

    (*what the admitted solutions of an entry make of its goal: node makes it of a goal and of
      its solutions, each a rule with what was made of its goals.  A solution that leads back to
      an entry under way is left out at that place, and so is one with a premise of which
      nothing is left*)
    fun build admitted (node: 'g -> ('r * ('a, ('c, 's) cell) premise list) list -> 'a) =
      let
        val memo = Unsynchronized.ref Keytab.empty;
        fun go key under_way =
          if member (op =) under_way key then (NONE, true)
          else
            (case Keytab.lookup (! memo) key of
              SOME made => (made, false)
            | NONE =>
                let
                  val {alts, ...} = the_entry key;
                  fun premise (Subgoal (g, k)) (SOME made, dep) =
                        let val (sols, dep') = go k (key :: under_way) in
                          (Option.map (fn sols => Subgoal (node g sols) :: made) sols,
                            dep orelse dep')
                        end
                    | premise (Condition c) (SOME made, dep) = (SOME (Condition c :: made), dep)
                    | premise _ none = none;
                  fun alternative i =
                    let val {rule, premises}: ('g, 'r, 'c, 's) alt = nth alts i in
                      fold premise premises (SOME [], false)
                      |>> Option.map (fn made => (rule, rev made))
                    end;
                  val made = map alternative (admitted_at admitted key);
                  val dep = exists #2 made;
                  val sols = (case map_filter #1 made of [] => NONE | sols => SOME sols);
                  val _ =
                    if dep then () else Unsynchronized.change memo (Keytab.update (key, sols));
                in (sols, dep) end);
      in fn key => #1 (go key []) end;

    (*a condition as it is given to the user where that has been made, else as written*)
    fun lenient ({raw, simplified, ...}: ('c, 's) cell) =
      (case ! simplified of SOME s => s | NONE => as_written raw);

    (*solutions as they go into a derivation; read: of a condition*)
    fun solutions read sols : ('g, 'r, 's) solution list =
      sols |> map (fn (rule, premises) =>
        {rule = rule,
         premises = map (map_premise I read) premises});
    fun derivation read goal sols = Derivation {goal = goal, solutions = solutions read sols};

    fun situation dist steps under_way : 'g situation =
      {dist = dist, steps = steps, under_way = under_way};

    (*the solutions of an entry solved without conditions: one, which leaves no condition to
      read*)
    fun unconditional_solutions key () =
      solutions lenient (the (build Keytab.empty (derivation lenient) key));

    (*a condition as it is given to the user: made when it is first read so*)
    fun strict ({raw, dist, steps, simplified}: ('c, 's) cell) =
      (case ! simplified of
        SOME s => s
      | NONE =>
          let val s = simplify (situation dist steps []) raw
          in simplified := SOME s; s end);


    (* the result *)

    (*the solutions admitted to the result, where they are more than the first*)
    val admitted = Unsynchronized.ref Keytab.empty;
    val in_result = Unsynchronized.ref Keytab.empty;
    (*the recorded solutions not yet judged, in the order of recording*)
    val pending = Unsynchronized.ref ([]: ((int * int) * int) list);
    (*the effective distance of the first solution of the top goal*)
    val first = Unsynchronized.ref (NONE: int option);
    (*nothing more is to enter the result*)
    val stopped = Unsynchronized.ref false;

    (*the conditions of the result, and the number of solutions that they show; read: of a
      condition*)
    fun evaluate read admitted =
      let
        fun node goal sols =
          leave reading goal (sols |> map (fn (_, premises) => map (map_premise I read) premises));
        val conj = clean reading (node top (the (build admitted node top_key)));
      in (conj, count conj) end;

    (*the entries that the admitted solutions use*)
    fun reach admitted =
      let
        fun visit key seen =
          if Keytab.defined seen key then seen
          else
            fold (fn i =>
                fold (fn Subgoal (_, k) => visit k | Condition _ => I)
                  (#premises (nth (#alts (the_entry key)) i)))
              (admitted_at admitted key) (Keytab.update (key, ()) seen);
      in visit top_key Keytab.empty end;

    (*a recorded solution enters the result, unless the result would then show too many
      solutions: then nothing more enters.  Its conditions are simplified for that; where that
      stops the search, the solution has not entered*)
    fun judge (key, i) =
      let
        val trial = Keytab.update (key, admitted_at (! admitted) key @ [i]) (! admitted);
        val (_, n) = evaluate strict trial;
      in
        if n > max_solution_number then stopped := true
        else
         (admitted := trial; in_result := reach trial;
          if n = max_solution_number then stopped := true else ())
      end;

    (*the recorded solutions of the entries in the result are judged, the earliest first*)
    fun judge_pending () =
      if ! stopped then ()
      else
        (case find_first (Keytab.defined (! in_result) o #1) (! pending) of
          SOME recorded =>
           (Unsynchronized.change pending (remove (op =) recorded);
            judge recorded; judge_pending ())
        | NONE => ());

    fun record key frame =
      let val i = length (#alts (the_entry key)) in
        map_entry key (fn {solved, alts, waiting} =>
          {solved = solved, alts = alts @ [alt_of frame], waiting = waiting});
        Unsynchronized.change pending (fn recorded => recorded @ [(key, i)]);
        if is_some (! first) then judge_pending () else ()
      end;


    (* a branch *)

    fun run (b as {eff, ncond, nrules, items, frames}: ('g, 'r, 'c) branch) =
      (case items of
        [] =>
          (*the conditions of the first solution are simplified now; where that stops the
            search, the others stay as they are written*)
         (first := SOME eff;
          ignore (evaluate strict (! admitted));
          if eff = 0 orelse max_solution_number <= 1 then stopped := true
          else (in_result := reach (! admitted); judge_pending ()))
      | Done {key, goal, eff = eff0, ncond = ncond0, nrules = nrules0} :: items' =>
          let
            val own as (own_eff, own_ncond, _) = (eff - eff0, ncond - ncond0, nrules - nrules0);
            val {solved, waiting, ...} = the_entry key;
          in
            (case solved of
              SOME (first_eff, _, _) =>
                (*recorded where it ties with the first solution, unless the first leaves no
                  leap to the user.  Only a branch that has waited by WAIT can come with a
                  cheaper one, which is dropped like a dearer one*)
                if own_eff = first_eff andalso first_eff > 0 then record key (hd frames) else ()
            | NONE =>
               (map_entry key (K {solved = SOME own, alts = [alt_of (hd frames)], waiting = []});
                if own_ncond = 0 andalso not (Inttab.defined (! unconditional_keys) (#1 key))
                then
                 (Unsynchronized.change unconditional_keys (Inttab.update (#1 key, key));
                  on_solved goal (unconditional_solutions key))
                else ();
                List.app push (rev waiting);
                run {eff = eff, ncond = ncond, nrules = nrules, items = items',
                  frames = close (goal, key) (tl frames)}))
          end
      | Todo {goal, dist, steps} :: items' =>
          let val ancestors = under_way items' in
            (case
              SOME (key_of (situation dist steps ancestors) goal)
                handle WAIT k => (wait k b; NONE) | ASIDE => NONE
             of
              NONE => ()
            | SOME id =>
                let val key = the_default (id, dist) (Inttab.lookup (! unconditional_keys) id) in
                  (case Keytab.lookup (! table) key of
                    SOME {solved = SOME (eff1, ncond1, nrules1), ...} =>
                      let
                        val b' =
                          {eff = eff + eff1, ncond = ncond + ncond1, nrules = nrules + nrules1,
                           items = items', frames = close (goal, key) frames};
                      in
                        if eff + eff1 >= max_leaps then ()
                        (*dearer now: other branches may come first*)
                        else if eff1 > 0 orelse ncond1 > 0 then push b'
                        else run b'
                      end
                  | SOME _ => wait key b
                  | NONE =>
                      (*not entered again while the same goal is being solved below on this
                        branch, at whatever distance*)
                      (case find_first (fn (_, k) => #1 k = id) ancestors of
                        SOME (_, k) => wait k b
                      | NONE => expand b key goal dist steps items'))
                end)
          end)

    and expand ({eff, ncond, nrules, frames, ...}: ('g, 'r, 'c) branch) key goal dist steps
        items' =
      let
        val _ =
          Unsynchronized.change table
            (Keytab.update (key, {solved = NONE, alts = [], waiting = []}));
        val done = Done {key = key, goal = goal, eff = eff, ncond = ncond, nrules = nrules};
        fun apply ({rule, premises, leap, user}: ('g, 'r, 'c) step) =
          let
            val goals = map_filter (fn Subgoal goal => SOME goal | Condition _ => NONE) premises;
            val conditional = length goals < length premises;
            val eff' = if conditional then eff + dist + leap else eff;
          in
            if unconditional andalso conditional then ()
            else if not (null goals) andalso steps + dist >= max_search_distance then ()
            else if eff' >= max_leaps then ()
            else
             (if user andalso conditional then user_rule () else ();
              push
               {eff = eff', ncond = if conditional then ncond + 1 else ncond,
                nrules = nrules + 1,
                items =
                  map (fn (g, keeps) =>
                    Todo {goal = g, dist = if keeps then dist else dist + leap, steps = steps + 1})
                    goals @ done :: items',
                frames =
                  {rule = rule, premises = premises, closed = [], dist = dist, steps = steps} ::
                    frames})
          end;
      in List.app apply (steps_of goal) end;


    (* the queue is worked off *)

    fun work () =
      if ! stopped then ()
      else
        (case Queue.min (! queue) of
          NONE => ()
        | SOME (key, b) =>
            (*no branch left that can tie with the first solution*)
            if (case ! first of SOME distance => hd key > distance | NONE => false) then ()
            else (Unsynchronized.change queue (Queue.delete key); run b; work ()));

    val cut_short =
      (push
        {eff = 0, ncond = 0, nrules = 0,
         items = [Todo {goal = top, dist = top_dist, steps = top_steps}], frames = []};
       work (); false)
      handle STOP => true;
  in
    (case ! first of
      NONE => Failed (if cut_short then User_Limit else No_Plan)
    | SOME distance =>
        let val (conditions, count) = evaluate lenient (! admitted) in
          Found
           {derivation =
              derivation lenient top (the (build (! admitted) (derivation lenient) top_key)),
            conditions = conditions, distance = distance, count = count, cut_short = cut_short}
        end)
  end;

(*the top goal is told first: a search that this stops, or whose top goal cannot be told,
  finds nothing*)
fun search (problem as {key, ...}: ('g, 'w, 'r, 'c, 's) problem) limits
    (start as {goal, dist, steps}) =
  (case
    SOME (SOME (key {dist = dist, steps = steps, under_way = []} goal) handle ASIDE => NONE)
      handle STOP => NONE
   of
    SOME (SOME id) => search_told problem limits start id
  | SOME NONE => Failed No_Plan
  | NONE => Failed User_Limit);

end;



(*** the search on the intro table ***)

signature CONCEPT_SEARCH =
sig
  val user_limit: int Config.T
  val max_search_distance: int Config.T
  val max_leaps: int Config.T
  val max_solution_number: int Config.T
  val has_applicable_rule: Proof.context -> term -> bool
  val search: {max_distance: int option} -> Proof.context -> term ->
    Concept_Intro_Table.derivation Concept_Intro_Table.result
  val search_unconditional: Proof.context -> term -> Concept_Intro_Table.derivation option
  val tidy: Proof.context -> Concept_Intro_Table.derivation ->
    {conditions: term list, proof: thm lazy}
  val prove: Proof.context -> Concept_Intro_Table.derivation -> thm
end;

structure Concept_Search: CONCEPT_SEARCH =
struct

structure Intro = Concept_Intro_Table;
structure Kernel = Concept_Search_Kernel;


(** options **)

val user_limit = Attrib.setup_config_int \<^binding>\<open>concept_fact_user_limit\<close> (K 30);
val max_search_distance =
  Attrib.setup_config_int \<^binding>\<open>concept_fact_max_search_distance\<close> (K 100);
val max_leaps = Attrib.setup_config_int \<^binding>\<open>concept_fact_max_leaps\<close> (K 20);
val max_solution_number =
  Attrib.setup_config_int \<^binding>\<open>concept_fact_max_solution_number\<close> (K 10);



(** goals and conditions **)

(*what stands around the fact of a concept premise !!xs. H1 ==> ... ==> Hn ==> C t (4.1 of the
  search plan): the parameters, each the name of its binder with the free variable that the
  fact and the hypotheses have for it, and the hypotheses.  Nothing stands around a fact where
  there are neither*)
type wrapper = {params: (string * (string * typ)) list, hyps: term list};

val no_wrapper: wrapper = {params = [], hyps = []};

fun same_wrapper ({params, hyps}: wrapper, {params = params', hyps = hyps'}: wrapper) =
  params = params' andalso eq_list (op aconv) (hyps, hyps');

(*a goal of a search around that is under way: that search, its entry*)
type mark = serial * (int * int);

(*What a search knows of a goal.  Untold: it has no form; the marks are the goals under way
  around the search that have kept it so.  Told: its form, and outside: its theorem, where
  another search of the call has proved it without conditions*)
datatype told =
    Untold of mark list
  | Told of {form: Intro.form, outside: thm lazy option};

(*prop: C t as written*)
type goal = {prop: term, told: told Unsynchronized.ref, wrapper: wrapper};

fun goal_of wrapper prop : goal =
  {prop = prop, told = Unsynchronized.ref (Untold []), wrapper = wrapper};

(*of a goal that has been told*)
fun told_of ({told, ...}: goal) =
  (case ! told of
    Told told' => told'
  | Untold _ => raise Fail "Concept_Search.told_of: a goal that is not told");
val form_prop_of = Intro.form_prop o #form o told_of;

(*a condition as a rule leaves it, with what the selector Simpset makes of it.  simp: cond ==
  what is given to the user, in beta-eta normal form like cond, where the two differ*)
type cond = {cond: term, simp: Intro.equation option};

val shown = Intro.shown_condition;

fun as_written cond : cond = {cond = cond, simp = NONE};

fun simplify ctxt cond : cond =
  {cond = cond,
   simp =
    if Concept_Type.may_rewrite ctxt cond then
      let
        val eq =
          Concept_Type.fixing ctxt [cond] (fn ctxt' => fn _ => fn fix =>
            (Concept_Type.selector_conv ctxt' then_conv Drule.beta_eta_conversion)
              (Thm.cterm_of ctxt' (fix cond)));
      in if Thm.is_reflexive eq then NONE else SOME (Lazy.value eq) end
    else NONE};

(*conditions are read as they are given to the user; wrapper: that of a goal*)
fun reading (wrapper: 'g -> wrapper) : ('g, wrapper, cond) Kernel.reading =
  {wrapper = (fn {params = [], hyps = []} => NONE | w => SOME w) o wrapper,
   trivial = fn c => shown c aconv \<^prop>\<open>True\<close>,
   same = fn (c, c') => shown c aconv shown c', same_wrapper = same_wrapper};



(** the rules on a goal **)

fun match ctxt form entry = Option.map (pair entry) (Intro.match_rule ctxt entry form);

fun has_applicable_rule ctxt goal =
  (case Intro.form_of_goal ctxt goal of
    SOME form => exists (is_some o match ctxt form) (Intro.entries_for ctxt form)
  | NONE => false);

(*how a goal is solved: by a rule on it, or as another search of this call has proved it: by
  the theorem of the form of the goal*)
datatype rule =
    Rule of {entry: Intro.entry, matched: Intro.matched}
  | Outside of thm lazy;

(*the leap of a rule on a goal (4.2 of the search plan): none for a rule that the system marks
  as safe, where the structure of the goal gives that of the rule; else the concept distance,
  at least 1 where it does not give it, and 1 more for an unsafe rule*)
fun leap ({safety, ...}: Intro.entry) ({concept_distance, how, ...}: Intro.matched) =
  let val reached = (case how of Intro.As_Written => true | Intro.Converted r => #reached r) in
    if safety = Intro.Safe_By_System andalso reached then 0
    else
      (if reached then concept_distance else Int.max (concept_distance, 1)) +
      (if safety = Intro.Unsafe then 1 else 0)
  end;

(*the wrapper of a concept premise and its fact: each !! gives a free variable of a new name,
  wherever it stands among the ==>, kept with the name of the binder*)
fun open_premise names prem =
  let
    fun strip (params, hyps) (\<^Const_>\<open>Pure.all T for \<open>Abs (x, _, body)\<close>\<close>) =
          let
            val x0 = (case Name.clean x of "" => "x" | x0 => x0);
            val x' = Unsynchronized.change_result names (Name.variant x0);
          in strip ((x0, (x', T)) :: params, hyps) (Term.subst_bound (Free (x', T), body)) end
      | strip (params, hyps) (\<^Const_>\<open>Pure.imp for hyp body\<close>) =
          strip (params, hyp :: hyps) body
      | strip (params, hyps) fact = ({params = rev params, hyps = rev hyps}: wrapper, fact);
  in strip ([], []) prem end;

(*The steps on a goal that has been told.  Proved by another search of the call: the one step
  that takes that theorem.  Else the rules on the goal, of the concept C on the structure t: a
  concept premise becomes a goal; it stays at the distance of the goal where it speaks of t
  itself, at C or at a concept that C gives.  Every other premise is a condition*)
fun steps ctxt names goal =
  (case told_of goal of
    {outside = SOME th, ...} => [{rule = Outside th, premises = [], leap = 0, user = false}]
  | {form, ...} =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val (C, _, t) = the (Intro.dest_fact thy (Intro.form_prop form));
        fun premise prem =
          if Intro.is_concept_premise thy prem then
            let
              val (wrapper, fact) = open_premise names prem;
              val (C', _, t') = the (Intro.dest_fact thy fact);
              val keeps =
                t' aconv t andalso
                  (C' = C orelse is_some (Concept_Package.entailment thy C C'));
            in Kernel.Subgoal (goal_of wrapper fact, keeps) end
          else Kernel.Condition prem;
        fun step (entry: Intro.entry, matched: Intro.matched) =
          {rule = Rule {entry = entry, matched = matched},
           premises = map premise (#premises matched), leap = leap entry matched,
           user = #user entry};
      in map step (map_filter (match ctxt form) (Intro.entries_for ctxt form)) end);



(** derivations **)

fun solution_of ({rule = Outside th, premises = _}: (goal, rule, cond) Kernel.solution) =
      Intro.Solution {entry = NONE, rule = th, converted = false, premises = []}
  | solution_of {rule = Rule {entry, matched}, premises} =
      Intro.Solution
       {entry = SOME entry, rule = #rule matched,
        converted =
          (case #how matched of Intro.As_Written => false | Intro.Converted _ => true),
        premises = map premise_of premises}
and premise_of (Kernel.Subgoal (derivation as Kernel.Derivation {goal, ...})) =
      let val {params, hyps} = #wrapper goal
      in Intro.Concept {params = params, hyps = hyps, derivation = derivation_of derivation} end
  | premise_of (Kernel.Condition c) = Intro.Remaining c
and derivation_of (Kernel.Derivation {goal, solutions}) =
  Intro.Goal
   {goal = #prop goal, form = Intro.form_equation (#form (told_of goal)),
    solutions = map solution_of solutions};



(** the conditions for the user **)

(*The conditions that a derivation leaves, made simpler (4.3 of the search plan), each as a
  proposition for the user in the order in which the derivation has them, and the theorem
  R1 ==> ... ==> Rr ==> conditions_of the derivation.

  The theorem is built along the derivation, with what holds at each place: the literals of the
  conditions, each with the theorem of its formula.  A disjunction among them is taken apart
  as soon as it holds, and what follows is done under each of its branches; under a wrapper,
  what the conditions have under the same wrapper holds too.  A goal is then proved by its
  first alternative all of whose premises hold.  So the derivation is walked once for each
  choice of branches: at most 2^(n - 1) times where the conditions show n solutions, which
  concept_fact_max_solution_number bounds*)
fun tidy ctxt derivation =
  let
    fun kernel_of wrapper (Intro.Goal {solutions, ...}) =
      Kernel.Derivation
       {goal = wrapper,
        solutions = solutions |> map (fn Intro.Solution {premises, ...} =>
          {rule = (),
           premises = premises |> map
            (fn Intro.Concept {params, hyps, derivation} =>
                  Kernel.Subgoal (kernel_of {params = params, hyps = hyps} derivation)
              | Intro.Remaining c => Kernel.Condition c)})};
    val read = reading I;
    val conj = Kernel.conditions read (kernel_of no_wrapper derivation);

    (*a proposition under a wrapper; a literal as a formula, and as the proposition for the
      user: a condition as it is shown, a disjunction as one formula, a literal under a wrapper
      as its proposition under the wrapper*)
    val under = Intro.under;
    fun formula (Kernel.Cond c) = Intro.formula_of (shown c)
      | formula (Kernel.Or branches) = foldr1 HOLogic.mk_disj (map conjunction branches)
      | formula (Kernel.Under (w, lit)) = Intro.formula_of (under_formula w lit)
    and conjunction lits = foldr1 HOLogic.mk_conj (map formula lits)
    and under_formula w lit = under w (HOLogic.mk_Trueprop (formula lit));
    fun prop (Kernel.Cond c) = shown c
      | prop (Kernel.Under (w, lit)) = under w (prop lit)
      | prop lit = HOLogic.mk_Trueprop (formula lit);
    (*the same proposition once*)
    val conditions = distinct (op aconv) (map prop conj);

    fun prove () =
      Concept_Type.fixing ctxt (Intro.derivation_terms derivation) (fn ctxt' => fn _ => fn fix =>
          let
            val cert = Thm.cterm_of ctxt' o fix;
            val formula_conv = Intro.formula_conv ctxt';

            val conj_intro = foldr1 (uncurry HOLogic.conj_intr);

            (*A from !!xs. Hs ==> A at the parameters of the wrapper, its hypotheses assumed;
              and back*)
            fun instance ({params, hyps}: wrapper) th =
              th |> fold (Thm.forall_elim o cert o Free o #2) params
              |> (fn th' => Drule.implies_elim_list th' (map (Thm.assume o cert) hyps));
            fun generalize ({params, hyps}: wrapper) th =
              th |> fold_rev (Thm.implies_intr o cert) hyps
              |> fold_rev (Thm.forall_intr o cert o Free o #2) params;

            (*the theorem of the formula of a literal, from that of its proposition*)
            fun fact (Kernel.Under (w, lit)) th =
                  fact lit (instance w th) |> generalize w |> Conv.fconv_rule formula_conv
              | fact (Kernel.Cond _) th = Conv.fconv_rule formula_conv th
              | fact (Kernel.Or _) th = th;

            (*what holds under a wrapper by a literal under the same wrapper*)
            fun opened w (Kernel.Under (w', lit), th) =
                  if #same_wrapper read (w, w') then
                    [(lit,
                      Thm.equal_elim
                        (Thm.symmetric (formula_conv (cert (under_formula w' lit)))) th
                      |> instance w')]
                  else []
              | opened _ _ = [];

            (*the same theorem under each branch of the disjunction th, if go_on gives one under
              each: then that theorem*)
            fun cases th branches go_on =
              (case branches of
                branch :: (rest as _ :: _) =>
                  let
                    val (P, Q) = (conjunction branch, formula (Kernel.Or rest));
                    val (cP, cQ) = apply2 (cert o HOLogic.mk_Trueprop) (P, Q);
                  in
                    (case (go_on (branch, Thm.assume cP), cases (Thm.assume cQ) rest go_on) of
                      (SOME th1, SOME th2) =>
                        SOME
                          (Drule.implies_elim_list
                            (Drule.infer_instantiate ctxt'
                              [(("P", 0), cert P), (("Q", 0), cert Q),
                               (("R", 0), Thm.dest_arg (Thm.cprop_of th1))] @{thm disjE})
                            [th, Thm.implies_intr cP th1, Thm.implies_intr cQ th2])
                    | _ => NONE)
                  end
              | _ => go_on (the_single branches, th));

            (*go_on with more literals that hold; a disjunction among them is taken apart*)
            fun with_facts [] known go_on = go_on known
              | with_facts ((Kernel.Or branches, th) :: more) known go_on =
                  cases th branches (fn (branch, th') =>
                    with_facts ((branch ~~ Concept_Package.conjuncts (length branch) th') @ more)
                      known go_on)
              | with_facts (held :: more) known go_on = with_facts more (held :: known) go_on;

            fun disj_intro rule (P, Q) th =
              Thm.implies_elim
                (Drule.infer_instantiate ctxt' [(("P", 0), cert P), (("Q", 0), cert Q)] rule) th;

            (*the theorem of what a derivation leaves, from the literals that hold*)
            fun goal known (Intro.Goal {goal = g, form, solutions}) =
              let
                fun alone solution =
                  Intro.conditions_of (Intro.Goal {goal = g, form = form, solutions = [solution]});
                fun all [] = SOME []
                  | all (p :: ps) =
                      (case premise known p of
                        SOME th => Option.map (cons th) (all ps)
                      | NONE => NONE);
                fun solved (Intro.Solution {premises, ...}) =
                  all premises |> Option.map (fn [] => @{thm TrueI} | ths => conj_intro ths);
                fun first [] = NONE
                  | first [solution] = solved solution
                  | first (solution :: more) =
                      let
                        val alternatives =
                          (alone solution, foldr1 HOLogic.mk_disj (map alone more));
                      in
                        (case solved solution of
                          SOME th => SOME (disj_intro @{thm disjI1} alternatives th)
                        | NONE => Option.map (disj_intro @{thm disjI2} alternatives) (first more))
                      end;
              in first solutions end
            and premise known (Intro.Remaining c) =
                  if #trivial read c then SOME @{thm TrueI}
                  else
                    known |> get_first
                      (fn (Kernel.Cond c', th) => if #same read (c, c') then SOME th else NONE
                        | _ => NONE)
              | premise known (Intro.Concept {params, hyps, derivation = d}) =
                  (case #wrapper read {params = params, hyps = hyps} of
                    NONE => goal known d
                  | SOME w =>
                      with_facts (maps (opened w) known) known (fn known' => goal known' d)
                      |> Option.map (Conv.fconv_rule formula_conv o generalize w));
          in
            with_facts (map (fn lit => (lit, fact lit (Thm.assume (cert (prop lit))))) conj) []
              (fn known => goal known derivation)
            |> the |> fold_rev (Thm.implies_intr o cert) conditions
          end);
  in {conditions = conditions, proof = Lazy.lazy prove} end;

(*R1 ==> ... ==> Rr ==> the goal of the derivation, as it was given to the search: the
  conditions for the user, and nothing else.  The schematic variables, those of the goal and
  those that the rules leave, are fixed while the theorem is made and come back as they were*)
fun prove ctxt derivation =
  let val tidied = Lazy.force (#proof (tidy ctxt derivation)) in
    Concept_Type.fixing ctxt (Thm.prop_of tidied :: Intro.derivation_terms derivation)
      (fn ctxt' => fn freeze => fn fix =>
        let
          val tidied' = freeze tidied;
          val conditions = Thm.cprems_of tidied';
        in
          Drule.implies_elim_list tidied' (map Thm.assume conditions)
          |> Intro.goal_thm ctxt' (Intro.map_derivation fix freeze derivation)
          |> Drule.implies_intr_list conditions
        end)
  end;



(** searches around a search **)

(*What a search tells the searches that the selector Simpset starts while it simplifies a goal
  or a condition for this one.  dist, steps: of that goal, or of the goal whose solution leaves
  the condition: a search inside goes on from them; under_way: the forms of the goals that are
  being solved on the branch of the goal, each with its entry*)
type level = {id: serial, dist: int, steps: int, under_way: (term * (int * int)) list};

(*a goal proved without conditions by a search of the call.  prems: the premises that the
  simplifier had assumed where that search ran: the theorem holds where they are assumed;
  by: that search; thm: of the form of the goal, made when it is first used*)
type proved = {prems: term list, by: serial, thm: thm lazy};

(*used, limit: of the steps of user rules that leave a condition, in all the searches of one
  call from outside; proved: what they have proved without conditions, by the forms of the
  goals, the earliest first; levels: of the searches around, the innermost first*)
structure Around = Proof_Data
(
  type T =
   {used: int Unsynchronized.ref, limit: int,
    proved: proved list Termtab.table Unsynchronized.ref, levels: level list} option;
  fun init _ = NONE;
);

(*A search ends without a solution free of conditions while goals of it cannot be told because
  of goals under way around it: the marks of those.  Each search around takes its own marks,
  where the branch waits for one of them and the goal is told again later, and passes the
  others on*)
exception GIVE_UP of mark list;



(** the search **)

(*the key of a goal: whether it is taken as proved by another search of the call, its form*)
structure Keys = Table(type key = bool * term val ord = prod_ord bool_ord Term_Ord.fast_term_ord);

(*max_leaps: no solution of this effective distance; unconditional: no rule that leaves a
  condition.  The limit on user rules stops the outermost search: a search inside another one
  passes the stop on*)
fun run {max_leaps = leaps, unconditional} ctxt0 prop =
  if is_none (Intro.dest_fact (Proof_Context.theory_of ctxt0) prop) then
    Intro.Failed Intro.Not_Concept_Goal
  else
    let
      val id = serial ();
      val around = Around.get ctxt0;
      val {used, limit, proved, levels} =
        (case around of
          SOME around => around
        | NONE =>
            {used = Unsynchronized.ref 0, limit = Config.get ctxt0 user_limit,
             proved = Unsynchronized.ref Termtab.empty, levels = []});
      (*the premises that the simplifier has assumed here*)
      val local_prems =
        Simplifier.prems_of ctxt0 |> map_filter (fn prem =>
          let val t = Thm.prop_of prem
          in if member (op aconv) (Thm.hyps_of prem) t then SOME t else NONE end);
      (*The context of this search, also for the theorems that are made of it later: without
        what the searches around tell, which holds only while they stand where they stood.  A
        unit of the selector Simpset that does not give its result has counted no user rule
        and proved nothing, unless a search that gives up ends it*)
      val ctxt =
        Around.put NONE ctxt0
        |> is_none around ? Concept_Type.restoring (fn () =>
            let val (n, tab) = (! used, ! proved)
            in fn SOME (GIVE_UP _) => () | _ => (used := n; proved := tab) end);
      fun user_rule () =
        if ! used >= limit then raise Kernel.STOP else Unsynchronized.inc used |> ignore;

      (*the context for what the selector Simpset does in a situation of this search*)
      fun inside ({dist, steps, under_way}: goal Kernel.situation) =
        let
          val level: level =
            {id = id, dist = dist, steps = steps,
             under_way = map (apfst form_prop_of) under_way};
        in
          ctxt |> Around.put
            (SOME {used = used, limit = limit, proved = proved, levels = level :: levels})
        end;

      (*the goals that a give-up or a goal under way around this search has kept untold, each
        once; a goal among them may have been told since*)
      val untold = Unsynchronized.ref ([]: goal list);
      fun set_marks (goal as {told, ...}: goal) marks =
        (told := Untold marks;
         Unsynchronized.change untold (insert (fn (g: goal, g': goal) => #told g = #told g') goal));
      (*the marks of the goals that are still untold*)
      fun outer_marks () =
        ! untold
        |> maps (fn {told, ...}: goal => (case ! told of Untold marks => marks | Told _ => []))
        |> distinct (op =);

      (*A goal is told when a branch takes it up, once.
        - A search that its form starts gives up.  Where goals of this search are among its
          marks, the branch waits for the innermost of them, and the goal is told again
          later; else the goal cannot be told here.
        - Another search of the call has proved the form where no more was assumed than here:
          that theorem is taken.
        - Else, where the form is under way around this search, the goal cannot be told here*)
      fun tell (situation: goal Kernel.situation) (goal as {prop, told, ...}: goal) =
        (case ! told of
          Told told' => told'
        | Untold _ =>
            let
              val form =
                the (Intro.form_of_goal (inside situation) prop)
                handle GIVE_UP marks =>
                  let val (own, outer) = List.partition (fn (id', _) => id' = id) marks in
                    set_marks goal outer;
                    (case
                      find_first (fn (_, key) => member (op =) (map #2 own) key)
                        (#under_way situation)
                     of
                      SOME (_, key) => raise Kernel.WAIT key
                    | NONE => raise Kernel.ASIDE)
                  end;
              val form_prop = Intro.form_prop form;
              val outside =
                Termtab.lookup_list (! proved) form_prop
                |> get_first (fn {prems, by, thm}: proved =>
                  if by <> id andalso subset (op aconv) (prems, local_prems) then SOME thm
                  else NONE);
              val _ =
                if is_some outside then ()
                else
                  (case
                    levels |> maps (fn {id, under_way, ...}: level =>
                      (case AList.lookup (op aconv) under_way form_prop of
                        SOME key => [(id, key)]
                      | NONE => []))
                   of
                    [] => ()
                  | marks => (set_marks goal marks; raise Kernel.ASIDE));
              val result = {form = form, outside = outside};
            in told := Told result; result end);

      (*the keys, numbered; a goal taken as proved is another goal than one of the same form
        that is not*)
      val keys = Unsynchronized.ref (Keys.empty: int Keys.table);
      fun key situation goal =
        let
          val {form, outside} = tell situation goal;
          val k = (is_some outside, Intro.form_prop form);
        in
          (case Keys.lookup (! keys) k of
            SOME n => n
          | NONE =>
              let val n = Keys.size (! keys)
              in keys := Keys.update (k, n) (! keys); n end)
        end;

      (*a goal of this search solved without conditions is proved for the call, unless one of
        its form is, where no more was assumed than here*)
      fun solved goal solutions =
        let val form_prop = form_prop_of goal in
          if exists (fn {prems, ...}: proved => subset (op aconv) (prems, local_prems))
              (Termtab.lookup_list (! proved) form_prop)
          then ()
          else
            Unsynchronized.change proved (Termtab.map_default (form_prop, []) (fn entries =>
              entries @
               [{prems = local_prems, by = id,
                 thm = Lazy.lazy (fn () =>
                  prove ctxt
                   (Intro.Goal
                     {goal = form_prop, form = NONE,
                      solutions = map solution_of (solutions ())}))}]))
        end;

      val names =
        Unsynchronized.ref
          (Variable.names_of (fold Variable.declare_term (prop :: local_prems) ctxt));
      (*a search inside another one goes on from the goal that started it, one step further*)
      val (start_dist, start_steps) =
        (case levels of {dist, steps, ...} :: _ => (dist, steps + 1) | [] => (0, 0));
      val max_solutions = Config.get ctxt max_solution_number;
      (*a search that gives up while a condition of this one is simplified goes through this
        one, with the marks of this one*)
      val found =
        Kernel.search
         {key = key, steps = steps ctxt names, user_rule = user_rule, solved = solved,
          simplify = simplify o inside, as_written = as_written, reading = reading #wrapper}
         {max_search_distance = Config.get ctxt max_search_distance, max_leaps = leaps,
          max_solution_number = max_solutions, unconditional = unconditional}
         {goal = goal_of no_wrapper prop, dist = start_dist, steps = start_steps}
        handle GIVE_UP marks => raise GIVE_UP (union (op =) (outer_marks ()) marks);
      (*without a solution free of conditions, a search gives up where goals of it are not
        told because of goals under way around it*)
      fun unless_untold result =
        (case outer_marks () of [] => result | marks => raise GIVE_UP marks);
    in
      (case found of
        Kernel.Found {derivation, conditions, distance, cut_short, ...} =>
          if cut_short andalso is_some around then raise Kernel.STOP
          else
            Intro.Found
             {value = derivation_of derivation,
              (*nothing was to be collected at the distance 0, nor where one solution is
                all that is wanted*)
              cut_short = cut_short andalso distance > 0 andalso max_solutions > 1}
            |> not (null conditions) ? unless_untold
      | Kernel.Failed Kernel.No_Plan => unless_untold (Intro.Failed Intro.No_Plan)
      | Kernel.Failed Kernel.User_Limit =>
          if is_some around then raise Kernel.STOP else Intro.Failed Intro.User_Limit)
    end;

(*max_distance: the greatest effective distance of a solution; else that of the option
  concept_fact_max_leaps, which is the least one not allowed*)
fun search {max_distance} ctxt prop =
  run
   {max_leaps = (case max_distance of SOME n => n + 1 | NONE => Config.get ctxt max_leaps),
    unconditional = false} ctxt prop;

fun search_unconditional ctxt prop =
  (case run {max_leaps = 1, unconditional = true} ctxt prop of
    Intro.Found {value, ...} => SOME value
  | Intro.Failed _ => NONE);

end;
