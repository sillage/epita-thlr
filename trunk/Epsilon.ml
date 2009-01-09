(**
    @author LAPOTRE GUILLAUME
    @author ALONE
  *)
open AlgorithmBase
open Automaton.StateKind


(*fonctions emprunt*)
let isInitial e =
  let l = (EpsilonAutomaton.State.label e) in
    l.initial

let listStates automaton =
  EpsilonAutomaton.Automaton.fold_state
    (fun a s -> a::s) automaton []

let findInitial auto =
  List.find (isInitial) (listStates auto)
(*n*)


let cr_st id = EpsilonAutomaton.State.create
  {identifier=id; initial=false; final=false}


let is_eps trans =
  ((EpsilonAutomaton.Transition.label trans)
   == Automaton.EpsilonAlphabet.Epsilon)


let list automat st =
  let liste = EpsilonAutomaton.Automaton.successors automat st
  in
    liste

let state_fst_eps automat =
  findInitial automat

(*  let etat =
    (EpsilonAutomaton.State.create {identifier=0 ;initial = true ;final=false})
in
  match (list automat etat) with
    |e::l -> (EpsilonAutomaton.Transition.src e)
    |[] -> etat
*)

let state_fst automat id =
  let etat =
    (LetterAutomaton.State.create {identifier=id ;initial = true ;final=false})
  in let automat = LetterAutomaton.Automaton.add_state automat etat
  in
    (automat,etat)


let give_label tr =
  match (EpsilonAutomaton.Transition.label tr) with
    |Automaton.EpsilonAlphabet.Letter(l)  -> Automaton.LetterAlphabet.Letter(l)
    | _ -> assert false

let finish auto_letter state =
  let {identifier=id;initial=ini;final=fin} = LetterAutomaton.State.label state
  in let auto_letter = LetterAutomaton.Automaton.remove_state auto_letter state
  in let auto_letter = LetterAutomaton.Automaton.add_state
      auto_letter
      (LetterAutomaton.State.create
      	 {identifier=id;initial=ini;final=true})
  in
    auto_letter

let rec no_eps_ls ls = match ls with
  |e::l -> if is_eps e then false
    else (no_eps_ls l)
  |[] -> true

let apply ~automaton =
  let rec nettoyage auto_letter auto_eps state_eps state nb_state l=
    match (l) with
      |e::l ->
	 if not(is_eps e)  then
	   let st = (LetterAutomaton.State.create
		       {identifier=(nb_state+1);initial=false;final=false})


	    in let trans =
	       LetterAutomaton.Transition.create
		 state
		 (give_label e)
		 st
	    in let auto_letter =
	       LetterAutomaton.Automaton.add_state
		 auto_letter
		 st


	    in let (auto_letter,nb_state) = nettoyage
	       auto_letter
	       auto_eps
	       (EpsilonAutomaton.Transition.dst e)
	       st
	       (nb_state+1)
	       (list auto_eps (EpsilonAutomaton.Transition.dst e))

	    in let (auto_letter,nb_state) = nettoyage
	       auto_letter
	       auto_eps
	       state_eps
	       state
	       (nb_state+1)
	       l

	    in let auto_letter =
	       LetterAutomaton.Automaton.add_transition
		 auto_letter
		 trans
	    in
	     (auto_letter,nb_state)
	 else
	   let (auto_letter,nb_state) = nettoyage
	     auto_letter
	     auto_eps
	     (EpsilonAutomaton.Transition.dst e)
	     state
	     nb_state
	     (list auto_eps (EpsilonAutomaton.Transition.dst e))
	   in let (auto_letter,nb_state) = nettoyage
	       auto_letter
	       auto_eps
	       state_eps
	       state
	       nb_state
	       l

	   in
	     (auto_letter,nb_state)

      |[] ->
	   if ((EpsilonAutomaton.Automaton.successors
		  auto_eps
		  state_eps)
	       ==
		  [])
	   then
	     (finish auto_letter state,nb_state)
	   else
	     (auto_letter,nb_state)



  in let (auto_letter,state) =  state_fst  LetterAutomaton.Automaton.empty 0
  in let state_eps =  (state_fst_eps automaton)
  in let (auto_letter,nb_state) = (nettoyage
				     auto_letter
				     automaton
				     state_eps
				     state
				     0
				     (EpsilonAutomaton.Automaton.successors automaton state_eps))
  in
    auto_letter


(*
let apply ~automaton =
  raise Not_implemented
*)
