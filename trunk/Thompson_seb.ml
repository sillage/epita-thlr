(**
    @author GISLAIS SEBASTIEN
    @author NOM2 PRENOM2
  *)
(* open AlgorithmBase *)
open Automaton
open AlgorithmBase.EpsilonAutomaton
open Re

let create_state id is_initial is_final =
  State.create
    { StateKind.identifier  = id ;
                initial     = is_initial ;
                final       = is_final }

let create_transition src label dst =
  Transition.create src label dst

let my_empty = Automaton.empty

let create_letter a =
  let s1 = create_state 1 true  false in
  let s2 = create_state 2 false true in
  let t1 = create_transistion s1 a s2 in
    ((List.fold_left
	Automaton.add_transition
	(List.fold_left
	   Automaton.add_state
	   my_empty
	   [ s1; s2 ])
	[ t1 ]),s1,s2)

let create_concatenation (a1, i1, f1) (a2, i2, f2) =
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
  (* Remove initial flag from i2 and final flag from f1: *)
  Automaton.map_state
    (fun s -> if s = i2 then
                State.create { (State.label i2) with StateKind.initial = false }
              else if s = f1 then
                State.create { (State.label f1) with StateKind.final = false }
              else
                s) r
(* Note that we do not need to create new transitions and nodes.
  This is because when used in a functional style, all these are shared by
  several automata with no trouble. *)

let create_union (a1, i1, f1) (a2, i2, f2) =
  raise Not_implemented

(*
let create_union a b =
  let s1 = create_state 1 true  false in
  let s2 = create_state 2 false false in
  let s3 = create_state 3 false false in
  let s4 = create_state 4 false false in
  let s5 = create_state 5 false false in
  let s6 = create_state 6 false true in
  let t1 = create_transition s1 EpsilonAlphabet.Epsilon s2 in
  let t2 = create_transition s2 a s3 in
  let t3 = create_transition s3 EpsilonAlphabet.Epsilon s6 in
  let t4 = create_transition s1 EpsilonAlphabet.Epsilon s4 in
  let t5 = create_transition s4 b s5 in
  let t6 = create_transition s5 EpsilonAlphabet.Epsilon s6 in
    List.fold_left
      Automaton.add_transition
      (List.fold_left
	 Automaton.add_state
	 my_empty
	 [ s1; s2 ; s3 ; s4 ; s5 ; s6 ])
      [ t1 ; t2 ; t3 ; t4 ; t5 ; t6 ]
*)

let create_repetition (a1, i1, f1) =
  raise Not_implemented

(*
let create_repetition a =
  let s1 = create_state 1 true  false in
  let s2 = create_state 2 false false in
  let s3 = create_state 3 false false in
  let s4 = create_state 4 false true in
  let t1 = create_transition s1 EpsilonAlphabet.Epsilon s2 in
  let t2 = create_transition s2 a s3 in
  let t3 = create_transition s3 EpsilonAlphabet.Epsilon s4 in
  let t4 = create_transition s3 EpsilonAlphabet.Epsilon s2 in
  let t5 = create_transition s1 EpsilonAlphabet.Epsilon s4 in
    List.fold_left
      Automaton.add_transition
      (List.fold_left
	 Automaton.add_state
	 my_empty
	 [ s1; s2 ; s3 ; s4 ])
      [ t1 ; t2 ; t3 ; t4 ; t5 ]
*)

let rec thompsonrec ~re =
  match re with
      Epsilon -> create_letter EpsilonAlphabet.Epsilon
    | Letter (a) -> create_letter (EpsilonAlphabet.Letter a)
    | BinaryOperation (Union,a,b) ->
	create_union (thompsonrec a) (thompsonrec b)
    | BinaryOperation (Concatenation,a,b) ->
	create_concatenation (thompsonrec a) (thompsonrec b)
    | UnaryOperation (Repetition,a) ->
	create_repetition (thompsonrec a)

let apply ~re = 
  match (thompsonrec re) with
      (a,ai,af) -> a
    | assert false


(* j'sais pas trop comment faire avec let _ : *)
let _ = apply re

(*
let apply ~re =
  raise Not_implemented
*)
