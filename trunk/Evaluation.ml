(**
    @author GANIVET JUSTIN
    @author LAPOTRE GUILLAUME
  *)
open AlgorithmBase



let listStates automaton =
  LetterAutomaton.Automaton.fold_state
    (fun a s -> a::s) automaton []

let isInitial e =
  let l = (LetterAutomaton.State.label e) in
    l.Automaton.StateKind.initial

let findInitial auto =
  List.find (isInitial) (listStates auto)

let isFinal e =
  let l = (LetterAutomaton.State.label e) in
    l.Automaton.StateKind.final

let give_label tr =
  match (LetterAutomaton.Transition.label tr) with
    |Automaton.LetterAlphabet.Letter(l)  -> l

let rec test_tr  mot  = function
    []->false
  | e::l when mot  = (give_label e)-> true
  | e::l -> test_tr mot  l

let rec give_dst  mot  = function
  | [] -> failwith ("boulet ca peut pa arriver")
  | e::l when mot  = (give_label e)-> (LetterAutomaton.Transition.dst e)
  | e::l -> give_dst mot  l

let rec main automate state = function
  | [] -> isFinal state
  | mot::l_mot ->
      begin
	let list_tr= LetterAutomaton.Automaton.successors automate state in
	if test_tr mot list_tr then
	  let dst = give_dst mot list_tr in
	    main automate dst l_mot
	else
	  false
      end




let apply ~automaton ~word =
  main automaton (findInitial automaton) word
