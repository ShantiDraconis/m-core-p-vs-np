import MCore.Real.P01InputNodePreservingPlan

namespace MCore
namespace Real
namespace P01PreservingMarkerIteration

open CanonicalFinalProof
open P01InputNodePreservingPlan

/-!
# Iterated reversible marker law

This is the algebraic induction needed by the physical unary driver.  It does
not invent a new producer: it proves that repeated local marker advances and
rewinds preserve the represented witness payload for an arbitrary finite
prefix.
-/

def splitPayload (prefix suffix : BitString) : BitString :=
  prefix ++ suffix

def advanceSpec : BitString → BitString → BitString × BitString
  | prefix, [] => (prefix, [])
  | prefix, b :: suffix => (prefix ++ [b], suffix)

def advanceN : Nat → BitString → BitString → BitString × BitString
  | 0, prefix, suffix => (prefix, suffix)
  | n + 1, prefix, suffix =>
      let p := advanceSpec prefix suffix
      advanceN n p.1 p.2

theorem advanceSpec_payload
    (prefix suffix : BitString) :
    let p := advanceSpec prefix suffix
    splitPayload p.1 p.2 = splitPayload prefix suffix := by
  cases suffix with
  | nil =>
      simp [advanceSpec, splitPayload]
  | cons b bs =>
      simp [advanceSpec, splitPayload, List.append_assoc]

theorem advanceN_payload
    (n : Nat) (prefix suffix : BitString) :
    let p := advanceN n prefix suffix
    splitPayload p.1 p.2 = splitPayload prefix suffix := by
  induction n generalizing prefix suffix with
  | zero =>
      simp [advanceN, splitPayload]
  | succ n ih =>
      simp only [advanceN]
      let p := advanceSpec prefix suffix
      have hstep : splitPayload p.1 p.2 = splitPayload prefix suffix :=
        advanceSpec_payload prefix suffix
      have hrest := ih p.1 p.2
      simpa [p] using hrest.trans hstep

theorem advanceN_zero
    (prefix suffix : BitString) :
    advanceN 0 prefix suffix = (prefix, suffix) := rfl

/-- If n is within the suffix length, n logical marker advances expose the nth
cell as the head of the remaining suffix while preserving the total payload. -/
theorem advanceN_exposes_getD
    (n : Nat) (prefix suffix : BitString)
    (h : n < suffix.length) :
    ∃ prefix' b tail,
      advanceN n prefix suffix = (prefix', b :: tail) ∧
      splitPayload prefix' (b :: tail) = splitPayload prefix suffix ∧
      b = suffix.getD n false := by
  induction n generalizing prefix suffix with
  | zero =>
      cases suffix with
      | nil =>
          simp at h
      | cons b tail =>
          refine ⟨prefix, b, tail, ?_, ?_, ?_⟩
          · rfl
          · rfl
          · simp [List.getD_cons_zero]
  | succ n ih =>
      cases suffix with
      | nil =>
          simp at h
      | cons b tail =>
          have ht : n < tail.length := by
            simpa using Nat.succ_lt_succ_iff.mp h
          have hih := ih (prefix := prefix ++ [b]) (suffix := tail) ht
          rcases hih with ⟨prefix', c, rest, hrun, hpayload, hget⟩
          refine ⟨prefix', c, rest, ?_, ?_, ?_⟩
          · simpa [advanceN, advanceSpec] using hrun
          · have hstep :
                splitPayload (prefix ++ [b]) tail =
                  splitPayload prefix (b :: tail) := by
                simp [splitPayload, List.append_assoc]
            exact hpayload.trans hstep
          · simpa [List.getD_cons_succ] using hget

/-- A full logical rewind is simply restoration to the original split.  The
physical inverse for each cell is markerRewind_layout. -/
def rewindSpec (originalPrefix originalSuffix : BitString) :
    BitString × BitString :=
  (originalPrefix, originalSuffix)

theorem advance_then_rewind_payload
    (n : Nat) (prefix suffix : BitString) :
    let p := advanceN n prefix suffix
    splitPayload (rewindSpec prefix suffix).1
      (rewindSpec prefix suffix).2 =
    splitPayload p.1 p.2 := by
  have h := advanceN_payload n prefix suffix
  simpa [rewindSpec] using h.symm

#print axioms MCore.Real.P01PreservingMarkerIteration.advanceN_payload
#print axioms MCore.Real.P01PreservingMarkerIteration.advanceN_exposes_getD
#print axioms MCore.Real.P01PreservingMarkerIteration.advance_then_rewind_payload

end P01PreservingMarkerIteration
end Real
end MCore
