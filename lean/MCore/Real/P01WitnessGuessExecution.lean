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
      simp only [NTM.runBranches, List.filter_append, List.flatMap_append]
      have hreassoc :
          (xs.filter (fun c =>
              witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state) ++
            ys.filter (fun c =>
              witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state)) ++
          ((xs.filter (fun c =>
              !(witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state))).flatMap
              witnessGuessMachine.successors ++
            (ys.filter (fun c =>
              !(witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state))).flatMap
              witnessGuessMachine.successors) =
          (xs.filter (fun c =>
              witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state) ++
            (xs.filter (fun c =>
              !(witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state))).flatMap
              witnessGuessMachine.successors) ++
          (ys.filter (fun c =>
              witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state) ++
            (ys.filter (fun c =>
              !(witnessGuessMachine.accepting c.state ||
                witnessGuessMachine.rejecting c.state))).flatMap
              witnessGuessMachine.successors) := by
        simp [List.append_assoc]
      rw [hreassoc, ih]

theorem witnessGuess_complete_from
    (left : List (Option Bool))
    (source witness : BitString)
    (hlen : witness.length = source.length) :
    doneConfig (witness.reverse.map some ++ left) ∈
      witnessGuessMachine.runBranches (source.length + 1)
        [guessConfig left source] := by
  induction source generalizing left witness with
  | nil =>
      have hwlen : witness.length = 0 := by simpa using hlen
      have hw : witness = [] := List.length_eq_zero_iff.mp hwlen
      subst witness
      simp [NTM.runBranches, witnessGuessMachine, guessConfig, doneConfig,
        NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  | cons b bs ih =>
      cases witness with
      | nil =>
          simp at hlen
      | cons w ws =>
          have hlen' : ws.length = bs.length := by
            simpa using Nat.succ.inj hlen
          have hstep :
              witnessGuessMachine.runBranches ((b :: bs).length + 1)
                  [guessConfig left (b :: bs)] =
                witnessGuessMachine.runBranches (bs.length + 1)
                  [ guessConfig (some false :: left) bs,
                    guessConfig (some true :: left) bs ] := by
            simp [NTM.runBranches, witnessGuessMachine, guessConfig_state,
              witnessGuess_successors_cons]
          rw [hstep]
          have hsplit :
              witnessGuessMachine.runBranches (bs.length + 1)
                  [ guessConfig (some false :: left) bs,
                    guessConfig (some true :: left) bs ] =
                witnessGuessMachine.runBranches (bs.length + 1)
                    [guessConfig (some false :: left) bs] ++
                  witnessGuessMachine.runBranches (bs.length + 1)
                    [guessConfig (some true :: left) bs] := by
            simpa using runBranches_append (bs.length + 1)
              [guessConfig (some false :: left) bs]
              [guessConfig (some true :: left) bs]
          rw [hsplit]
          cases w with
          | false =>
              have hmem := ih (some false :: left) ws hlen'
              have htarget :
                  doneConfig (ws.reverse.map some ++ some false :: left) ∈
                    witnessGuessMachine.runBranches (bs.length + 1)
                      [guessConfig (some false :: left) bs] := by
                simpa [List.append_assoc] using hmem
              exact List.mem_append_left _ htarget
          | true =>
              have hmem := ih (some true :: left) ws hlen'
              have htarget :
                  doneConfig (ws.reverse.map some ++ some true :: left) ∈
                    witnessGuessMachine.runBranches (bs.length + 1)
                      [guessConfig (some true :: left) bs] := by
                simpa [List.append_assoc] using hmem
              exact List.mem_append_right _ htarget

theorem witnessGuess_complete
    (source witness : BitString)
    (hlen : witness.length = source.length) :
    doneConfig (witness.reverse.map some) ∈
      witnessGuessMachine.runBranches (source.length + 1)
        [guessConfig [] source] := by
  simpa using witnessGuess_complete_from [] source witness hlen

theorem witnessGuess_halts_from
    (left : List (Option Bool))
    (source : BitString) :
    witnessGuessMachine.HaltsWithin (source.length + 1)
      (guessConfig left source) := by
  unfold NTM.HaltsWithin
  induction source generalizing left with
  | nil =>
      intro reached hmem
      simp [NTM.runBranches, witnessGuessMachine, guessConfig, doneConfig,
        NTM.successors, NTM.stepBranch, Tape.write, Tape.move] at hmem
      subst reached
      exact Or.inl (doneConfig_accepting left)
  | cons b bs ih =>
      intro reached hmem
      have hstep :
          witnessGuessMachine.runBranches ((b :: bs).length + 1)
              [guessConfig left (b :: bs)] =
            witnessGuessMachine.runBranches (bs.length + 1)
              [ guessConfig (some false :: left) bs,
                guessConfig (some true :: left) bs ] := by
        simp [NTM.runBranches, witnessGuessMachine, guessConfig_state,
          witnessGuess_successors_cons]
      rw [hstep] at hmem
      have hsplit :
          witnessGuessMachine.runBranches (bs.length + 1)
              [ guessConfig (some false :: left) bs,
                guessConfig (some true :: left) bs ] =
            witnessGuessMachine.runBranches (bs.length + 1)
                [guessConfig (some false :: left) bs] ++
              witnessGuessMachine.runBranches (bs.length + 1)
                [guessConfig (some true :: left) bs] := by
        simpa using runBranches_append (bs.length + 1)
          [guessConfig (some false :: left) bs]
          [guessConfig (some true :: left) bs]
      rw [hsplit] at hmem
      rcases List.mem_append.mp hmem with hfalse | htrue
      · exact ih (some false :: left) reached hfalse
      · exact ih (some true :: left) reached htrue

theorem witnessGuess_halts
    (source : BitString) :
    witnessGuessMachine.HaltsWithin (source.length + 1)
      (guessConfig [] source) :=
  witnessGuess_halts_from [] source

#print axioms MCore.Real.P01WitnessGuessExecution.runBranches_append
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_complete_from
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_complete
#print axioms MCore.Real.P01WitnessGuessExecution.witnessGuess_halts

end P01WitnessGuessExecution
end Real
end MCore
