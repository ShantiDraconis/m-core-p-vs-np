import MCore.Real.P01GlobalParserSimulation

namespace MCore
namespace Real
namespace P01GlobalParserRuntime

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATParserLeafPopProof
open CanonicalSATParserLeafReturnProof
open CanonicalSATParserLeafSourceProof
open CanonicalSATParserWorkScanProof
open CanonicalSATSlotLog
open MachineRunLemmas
open P01GlobalParserSimulation

private theorem map_some_false_suffix
    (suffix : SlotLog)
    (hall : ∀ b ∈ suffix, b = false) :
    suffix.map some =
      List.replicate suffix.length (some false) := by
  have hs :=
    CanonicalSATParserLeafPopProof.all_false_eq_replicate suffix hall
  rw [hs]
  simp

/-- Exact step count for the physical leaf-pop path when an older active slot
remains.  The source-check state is reached in exactly log.length+1 steps. -/
theorem leaf_afterEnd_active_to_source_exact
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    parserMachine.run (log.length + 1)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft
          13 (none :: sourceLeft) log none) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
        17 sourceLeft (log'.map some ++ [none]) := by
  rcases popSlot_decompose log log' hpop with
    ⟨pre, suffix, hlog, hlog', hsuffix⟩
  have hszero : activeSlots suffix = 0 :=
    (activeSlots_eq_zero_iff_all_false suffix).mpr hsuffix
  have hpre : activeSlots pre ≠ 0 := by
    intro hz
    apply hactive
    rw [hlog', activeSlots_append]
    simp [activeSlots, hz, hszero]
  have hpreRev : activeSlots pre.reverse ≠ 0 := by
    simpa [P01GlobalParserSimulation.activeSlots_reverse] using hpre
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  have hlen :
      log.length + 1 =
        (suffix.length + 1) + (pre.length + 1) := by
    rw [hlog]
    simp [List.length_append]
    omega
  rw [hlen, MachineRunLemmas.run_add, hlog]
  rw [CanonicalSATParserLeafPopProof.leaf_pop_decomposed
    pre suffix (none :: sourceLeft) hsuffix]
  rw [CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check]
  have hscan :=
    CanonicalSATParserLeafReturnProof.leaf14_active_run
      pre.reverse sourceLeft
      (some false ::
        (List.replicate suffix.length (some false) ++ [none]))
      hpreRev
  calc
    parserMachine.run (pre.length + 1)
        (CanonicalSATParserLeafReturnProof.leafCheckConfig 14
          pre.reverse sourceLeft
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 17
        sourceLeft
        (pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) := by
      simpa using hscan
    _ =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 17
        sourceLeft (log'.map some ++ [none]) := by
      exact congrArg
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          (17 : Fin 25) sourceLeft)
        hright

/-- Exact step count for the physical leaf-pop path when no active slot
remains. -/
theorem leaf_afterEnd_inactive_to_source_exact
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    parserMachine.run (log.length + 1)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft
          13 (none :: sourceLeft) log none) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
        16 sourceLeft (log'.map some ++ [none]) := by
  rcases popSlot_decompose log log' hpop with
    ⟨pre, suffix, hlog, hlog', hsuffix⟩
  have hszero : activeSlots suffix = 0 :=
    (activeSlots_eq_zero_iff_all_false suffix).mpr hsuffix
  have hprezero : activeSlots pre = 0 := by
    rw [hlog', activeSlots_append] at hzero
    simpa [activeSlots, hszero] using hzero
  have hpreall : ∀ b ∈ pre, b = false :=
    (activeSlots_eq_zero_iff_all_false pre).mp hprezero
  have hpreRevAll : ∀ b ∈ pre.reverse, b = false := by
    intro b hb
    exact hpreall b (by simpa using hb)
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  have hlen :
      log.length + 1 =
        (suffix.length + 1) + (pre.length + 1) := by
    rw [hlog]
    simp [List.length_append]
    omega
  rw [hlen, MachineRunLemmas.run_add, hlog]
  rw [CanonicalSATParserLeafPopProof.leaf_pop_decomposed
    pre suffix (none :: sourceLeft) hsuffix]
  rw [CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check]
  have hscan :=
    CanonicalSATParserLeafReturnProof.leaf14_all_false_run
      pre.reverse sourceLeft
      (some false ::
        (List.replicate suffix.length (some false) ++ [none]))
      hpreRevAll
  calc
    parserMachine.run (pre.length + 1)
        (CanonicalSATParserLeafReturnProof.leafCheckConfig 14
          pre.reverse sourceLeft
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
        sourceLeft
        (pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) := by
      simpa using hscan
    _ =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
        sourceLeft (log'.map some ++ [none]) := by
      exact congrArg
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          (16 : Fin 25) sourceLeft)
        hright

/-- Exact active-leaf return count through source rewind. -/
theorem leaf_afterEnd_roundtrip_nonempty_active_exact
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ConfigRightBlankEq
      (parserMachine.run
        ((log.length + 1) + (rest.length + 2))
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: some last ::
            (rest.map some ++
              List.replicate pad (none : Option Bool)))
          log none))
      (phaseConfig 4 pad (rest.reverse ++ [last]) log') := by
  let sourceLeft : List (Option Bool) :=
    some last ::
      (rest.map some ++ List.replicate pad (none : Option Bool))
  rw [MachineRunLemmas.run_add]
  have hsource :=
    leaf_afterEnd_active_to_source_exact
      sourceLeft log log' hpop hactive
  rw [show
      parserMachine.run (log.length + 1)
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
          (none :: some last ::
            (rest.map some ++
              List.replicate pad (none : Option Bool)))
          log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some ++ [none]) by
      simpa [sourceLeft] using hsource]
  have hcfg :=
    P01GlobalParserSimulation.leafSourceCheck_trailing_blank
      (17 : Fin 25) sourceLeft (log'.map some)
  have hrun :=
    P01GlobalParserSimulation.parser_run_respects_right_blank
      (rest.length + 2) hcfg
  have hcanon :=
    CanonicalSATParserLeafSourceProof.leaf17_roundtrip_to_phase
      pad hpad last rest log'
  have hcanon' :
      parserMachine.run (rest.length + 2)
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some)) =
        phaseConfig 4 pad (rest.reverse ++ [last]) log' := by
    simpa [sourceLeft] using hcanon
  rw [hcanon'] at hrun
  exact hrun

#print axioms MCore.Real.P01GlobalParserRuntime.leaf_afterEnd_active_to_source_exact
#print axioms MCore.Real.P01GlobalParserRuntime.leaf_afterEnd_inactive_to_source_exact
#print axioms MCore.Real.P01GlobalParserRuntime.leaf_afterEnd_roundtrip_nonempty_active_exact

end P01GlobalParserRuntime
end Real
end MCore
