(**
   @author Ganivet Justin
   @author Lapotre Guillaume
*)
open Automaton
(* Import all functions and types from module AlgorithmBase.EpsilonAutomaton: *)
open AlgorithmBase.EpsilonAutomaton



let create_state id is_initial is_final =
  State.create
    { StateKind.identifier  = id ;
      initial     = is_initial ;
      final       = is_final }

let create_transition src label dst =
  Transition.create src label dst
    (* label must be something of value AlgorithmBase.EpsilonAutomaton.Alphabet.t,
       here Automaton.EpsilonAlphabet.t *)
    (* If used with LetterAutomaton, it must be of type Automaton.LetterAlphabet.t *)

(* "my_empty" is the empty automaton. *)
let my_empty = Automaton.empty
  (* Here Automaton is AlgorithmBase.EpsilonAutomaton.Automaton module. *)
  (* my_empty is an alias to Automaton.empty as everything is a constant in
     functional programming. *)


let concat (a1,i1,f1) (a2,i2,f2) =
  (* Create new automaton with states from a1 and a2: *)
  (* Automaton.fold_state f a base computes:
     f ( sn, ... f ( s2, f (s1, base) ) ) where s1..sn are the states of
     the automaton.
     Here "f" is a wrapper around Automaton.add_state (because arguments are in
     wrong order, and "a" is an empty automaton. *)
  let a' = Automaton.fold_state
    (fun s a -> Automaton.add_state a s) a2
    (Automaton.fold_state (fun s a -> Automaton.add_state a s) a1 my_empty) in
    (* Add all transitions from a1 and a2: *)
  let a'' = Automaton.fold_transition
    (fun t a -> Automaton.add_transition a t) a2
    (Automaton.fold_transition (fun t a -> Automaton.add_transition a t) a1 a') in
    (* Add epsilon-transition from f1 to i2: *)
  let r = Automaton.add_transition a''
    (create_transition f1 EpsilonAlphabet.Epsilon i2) in

  let i3 = create_state (Automaton.nb_states r) true false in
  let f3 = create_state (Automaton.nb_states r + 1)  false true in
  let t1 = create_transition i3 EpsilonAlphabet.Epsilon i1 in
  let t2 = create_transition f2 EpsilonAlphabet.Epsilon f3 in
    (* create les states supplementaire pour Tompson *)
  let b = List.fold_left
    Automaton.add_state r [i3;f3] in
  let c = List.fold_left
    Automaton.add_transition b [t1;t2] in
    (* on ajoute les transitions et les states a l'automate *)
    (Automaton.map_state
	(fun s -> if s = i2 then
           State.create { (State.label i2) with StateKind.initial = false }
         else if s = f1 then
           State.create { (State.label f1) with StateKind.final = false }
         else if s = i1 then
	   State.create { (State.label i1) with StateKind.initial = false }
	 else if s = f2 then
	   State.create { (State.label f2) with StateKind.final = false }
        else
	  s)
	c,i3,f3)
      (* Remove initial flag from i2 and final flag from f1: *)


let aytoile (a,i,f) =


  let i1 = create_state (Automaton.nb_states a) true false in
  let f1 = create_state ((Automaton.nb_states a) + 1) false true in
  let t1 = create_transition i1 EpsilonAlphabet.Epsilon f1 in
  let t2 = create_transition f EpsilonAlphabet.Epsilon i in

  let a =
    List.fold_left  Automaton.add_transition
      (List.fold_left Automaton.add_state a [ i1 ; f1])
      [ t1 ; t2]
  in

    ((Automaton.map_state
	(fun s -> if s = i then
           State.create { (State.label i) with StateKind.initial = false }
	 else if s = f then
           State.create { (State.label f) with StateKind.final = false }
	 else
           s) a),i,f)
let plusse (a1,i1,f1) (a2,i2,f2) =


  let a = Automaton.fold_state
    (fun s a -> Automaton.add_state a s) a2
    (Automaton.fold_state (fun s a -> Automaton.add_state a s) a1 my_empty) in
    (* Add all transitions from a1 and a2: *)
  let b = Automaton.fold_transition
    (fun t a -> Automaton.add_transition a t) a2
    (Automaton.fold_transition (fun t a -> Automaton.add_transition a t) a1 a) in

  let i3 = create_state (Automaton.nb_states b) true false in
  let f3 = create_state ((Automaton.nb_states b) + 1) false true in
  let t1 = create_transition i3 EpsilonAlphabet.Epsilon i1 in
  let t2 = create_transition i3 EpsilonAlphabet.Epsilon i2 in
  let t3 = create_transition f1 EpsilonAlphabet.Epsilon f3 in
  let t4 = create_transition f2 EpsilonAlphabet.Epsilon f3 in


  let c =
    List.fold_left  Automaton.add_transition
      (List.fold_left Automaton.add_state b [ i3 ; f3])
      [ t1 ; t2 ; t3 ; t4]
  in
    (Automaton.map_state
	(fun s -> if s = i2 then
           State.create { (State.label i2) with StateKind.initial = false }
         else if s = f1 then
           State.create { (State.label f1) with StateKind.final = false }
         else if s = i1 then
	   State.create { (State.label i1) with StateKind.initial = false }
	 else if s = f2 then
	   State.create { (State.label f2) with StateKind.final = false }
        else
	  s) c ,
     i3,f3)

let eps  =
  let s1 = create_state 0 true false in
  let s2 = create_state 1 false true in
  let t1 = create_transition s1 EpsilonAlphabet.Epsilon s2 in

  ((List.fold_left
    Automaton.add_transition
    (List.fold_left
      Automaton.add_state
      my_empty
      [ s1 ; s2  ])
    [ t1 ]),s1,s2)

let lettre x =
  let s1 = create_state 0 true false in
  let s2 = create_state 1 false true in
  let t1 = create_transition s1 (EpsilonAlphabet.Letter (x)) s2 in

  ((List.fold_left
    Automaton.add_transition
    (List.fold_left
      Automaton.add_state
      my_empty
      [ s1 ; s2  ])
    [ t1 ]),s1,s2)



let rec kikoo =function
    Re.Epsilon -> eps
  | Re.Letter (x) -> lettre x
  | Re.BinaryOperation (binop,exp1,exp2) ->
      if binop = Re.Union then plusse (kikoo exp1) (kikoo exp2)
      else if binop = Re.Concatenation then concat (kikoo exp1) (kikoo exp2)
      else
	assert false

  | Re.UnaryOperation (uniop,exp1) ->
      if uniop = Re.Repetition then (kikoo exp1)
      else
	assert false



let apply ~re =
  let kik = kikoo re in
    match kik with
      | (a,i,f) -> a
      | _ -> assert false
