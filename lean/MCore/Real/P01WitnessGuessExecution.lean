import MCore.Real.CanonicalSATWitnessGuessNTM

namespace MCore
namespace Real
namespace P01WitnessGuessExecution

open CanonicalFinalProof
open CanonicalSATWitnessGuessNTM

theorem runBranches_append
    (fuel : Nat)
    (xs ys : List (Configuration (Fin 2) (Option Bool))) :
    witnessGuessMachine.runBranches fuel (xs ++ ys) =
      witnessGuessMachine.runBranches fuel xs ++
        witnessGuessMachine.runBranches fuel ys := by
  induction fuel generalizing xs ys with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [NTM.runBranches]
      rw [List.filter_append, List.filter_append, List.flatMap_append]
      rw [List.append_assoc, ← List.append_assoc
        (List.filter (fun c => !(witnessGuessMachine.accepting c.state ||
          witnessGuessMachine.rejecting c.state)) xs).flatMap
            witnessGuessMachine.successors]
      rw [ih]
      simp only [List.append_assoc]

theorem witnessGuess_complete_from
    (left : List (Option Bool))
    (source witness : BitString)
    (hlen : witness.length = source.length) :
    doneConfig (witness.reverse.map some ++ left) ∈
      witnessGuessMachine.runBranches (source.length + 1)
        [guessConfig left source] := by
  induction source generalizing left witness with
  | nil =>
      have hw : witness = [] := by
        simpa using List.length_eq_zero.mp (by simpa using hlen)
      subst witness
      simp [NTM.runBranches, witnessGuess_successors_nil,
        guessConfig, witnessGuessMachine, doneConfig]
  | cons b bs ih =>
      cases witness with
      | nil =>
          simp at hlen
      | cons w ws =>
          have hlen' : ws.length = bs.length := by
            simpa using Nat.succ.inj hlen
          rw [List.length_cons]
          simp only [NTM.runBranches]
          have hsucc := witnessGuess_successors_cons left b bs
          simp [witnessGuessMachine, guessConfig_state, hsucc]
          rw [runBranches_append]
          cases w with
          | false =>
              have hmem := ih (some false :: left) ws hlen'
              simpa [List.reverse_cons, List.map_append, List.append_assoc] using
                List.mem_append_left _ hmem
          | true =>
              have hmem := ih (some true :: left) ws hlen'
              simpa [List.reverse_cons, List.map_append, List.append_assoc] using
                List.mem_append_right _ hmem

theorem witnessGuess_complete
    (source witness : BitString)
    (hlen : witness.length = source.length) :
    doneConfig (witness.reverse.map some) ∈
      witnessGuessMachine.runBranches (source.length + 1)
        [guessConfig [] source] := by
  simpa using witnessGuess_complete_from [] source witness hlen

#print axioms MCore.Real.P01WitnessGuessExecution.runBranches_append
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_complete_from
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_complete

end P01WitnessGuessExecution
end Real
end MCore
