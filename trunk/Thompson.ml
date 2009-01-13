(**
    @author GISLAIS SEBASTIEN
    @author LADEVIE STEPHANE
  *)
open AlgorithmBase
open Automaton
open Automaton.StateKind
open Re

let kikoo = EpsilonAutomaton.Automaton.empty
let debut = EpsilonAutomaton.State.create { identifier=0; initial=true;final=false}
let kikoo =  EpsilonAutomaton.Automaton.add_state kikoo (debut)

let add_letter auto id letter =
  let state1 =  EpsilonAutomaton.State.create { identifier=id+1; initial=false;final=false}in
  let state2 =  EpsilonAutomaton.State.create { identifier=id + 2; initial=false;final=false} in
  let auto = EpsilonAutomaton.Automaton.add_state auto state1 in
  let auto = EpsilonAutomaton.Automaton.add_state auto state2 in
  let t = EpsilonAutomaton.Transition.create state1 letter state2 in
  let auto = EpsilonAutomaton.Automaton.add_transition auto t in
    (auto,id+2,state1,state2);;



let apply ~re =

  let rec thompson re auto id =
    match re with
      |Re.Letter(l) ->  add_letter auto id (EpsilonAlphabet.Letter(l))

      |Re.BinaryOperation(Re.Union,l,r) ->
         let (a1,i1,s1,s2) = (thompson l auto (id+1)) in
         let (a2,i2,s3,s4) = (thompson r a1 i1) in
	 let sini = EpsilonAutomaton.State.create {identifier=id+1;initial=false;final=false} in
	 let a2 = EpsilonAutomaton.Automaton.add_state a2 sini in
         let t1 = EpsilonAutomaton.Transition.create sini EpsilonAlphabet.Epsilon s1 in
         let t3 = EpsilonAutomaton.Transition.create sini EpsilonAlphabet.Epsilon s3 in
         let a2 = EpsilonAutomaton.Automaton.add_transition a2 t1 in
         let a2 = EpsilonAutomaton.Automaton.add_transition a2 t3 in
         let s5 = EpsilonAutomaton.State.create {identifier=i2+1;initial=false;final=false} in
         let a2 = EpsilonAutomaton.Automaton.add_state a2 s5 in
         let t2 = EpsilonAutomaton.Transition.create s2 EpsilonAlphabet.Epsilon s5 in
         let t4 = EpsilonAutomaton.Transition.create s4 EpsilonAlphabet.Epsilon s5 in
         let a2 = EpsilonAutomaton.Automaton.add_transition a2 t2 in
         let a2 = EpsilonAutomaton.Automaton.add_transition a2 t4 in
           (a2,i2+2,sini,s5)

      |Re.BinaryOperation(Re.Concatenation, l, r) ->
         let (a1,i1,s1,s2) = (thompson l auto id) in
        let (a2,i2,s3,s4) = (thompson r a1 i1) in
        let t2 = EpsilonAutomaton.Transition.create s2 EpsilonAlphabet.Epsilon s3 in
        let a2 = EpsilonAutomaton.Automaton.add_transition a2 t2 in
          (a2,i2,s1,s4)

      |Re.UnaryOperation(Re.Repetition,arg) ->
	 let (a1,i1,s1,s2) = thompson arg auto (id+1) in
	 let sini = EpsilonAutomaton.State.create {identifier=id+1;initial=false;final=false} in
	 let a1 = EpsilonAutomaton.Automaton.add_state a1 sini in
	 let t1 = EpsilonAutomaton.Transition.create sini EpsilonAlphabet.Epsilon s1 in
	 let a1 = EpsilonAutomaton.Automaton.add_transition a1 t1 in
	 let t1 = EpsilonAutomaton.Transition.create s2 EpsilonAlphabet.Epsilon s1 in
	 let a1 = EpsilonAutomaton.Automaton.add_transition a1 t1 in
	 let s3 = EpsilonAutomaton.State.create {identifier=i1+1;initial=false;final=false} in
	 let a1 = EpsilonAutomaton.Automaton.add_state a1 s3 in
	 let t1 = EpsilonAutomaton.Transition.create s2 EpsilonAlphabet.Epsilon s3 in
	 let a1 = EpsilonAutomaton.Automaton.add_transition a1 t1 in
	 let t1 = EpsilonAutomaton.Transition.create sini EpsilonAlphabet.Epsilon s3 in
	 let a1 = EpsilonAutomaton.Automaton.add_transition a1 t1 in
         (a1,i1+1,sini,s3)

      |Re.Epsilon -> add_letter (auto) id (EpsilonAlphabet.Epsilon)

  in
  let auto_fin auto re debut =
    let (a1,id,si,sf) = thompson re auto 0 in
    let state1 =  EpsilonAutomaton.State.create { identifier=id+1; initial=false;final=true} in
    let a1 = EpsilonAutomaton.Automaton.add_state a1 state1 in
    let t1 = EpsilonAutomaton.Transition.create debut (EpsilonAlphabet.Epsilon) si in
    let a1 = EpsilonAutomaton.Automaton.add_transition a1 t1 in
    let t1 = EpsilonAutomaton.Transition.create sf (EpsilonAlphabet.Epsilon) state1 in
    let a1 = EpsilonAutomaton.Automaton.add_transition a1 t1 in
      a1
  in auto_fin kikoo re debut;;

