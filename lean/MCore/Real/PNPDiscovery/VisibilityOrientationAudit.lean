import MCore.Real.PNPDiscovery.SourceHiddenGrowthExpansion
import MCore.Real.PNPDiscovery.ReadCone

namespace MCore
namespace Real
namespace PNPDiscovery

/-- A concrete bit mismatch before k prevents equality of k-prefixes, provided
the mismatching bit exists in both strings. -/
theorem visible_bit_mismatch_prevents_prefix_equality
    (x y : BitString)
    (k q : Nat)
    (hqk : q < k)
    (hqx : q < x.length)
    (hqy : q < y.length)
    (hDiff : x.getD q false ≠ y.getD q false) :
    x.take k ≠ y.take k := by
  intro hTake
  have hx :
      (x.take k).getD q false = x.getD q false := by
    have hqtk : q < (x.take k).length := by
      simp [List.length_take, Nat.min_def, hqx, hqk]
      omega
    induction x generalizing k q with
    | nil =>
        simp at hqx
    | cons a as ih =>
        cases q with
        | zero =>
            simp [List.getD_cons_zero]
        | succ q =>
            cases k with
            | zero =>
                omega
            | succ k =>
                have hqx' : q < as.length := by simpa using hqx
                have hqk' : q < k := by omega
                simpa [List.getD_cons_succ] using
                  ih k q hqk' hqx'
  have hy :
      (y.take k).getD q false = y.getD q false := by
    have hqtk : q < (y.take k).length := by
      simp [List.length_take, Nat.min_def, hqy, hqk]
      omega
    induction y generalizing k q with
    | nil =>
        simp at hqy
    | cons a as ih =>
        cases q with
        | zero =>
            simp [List.getD_cons_zero]
        | succ q =>
            cases k with
            | zero =>
                omega
            | succ k =>
                have hqy' : q < as.length := by simpa using hqy
                have hqk' : q < k := by omega
                simpa [List.getD_cons_succ] using
                  ih k q hqk' hqy'
  have := congrArg (fun bs : BitString => bs.getD q false) hTake
  rw [hx, hy] at this
  exact hDiff this

/-- Correct orientation audit:
readCone invisibility consumes EQUALITY of the whole shared prefix.
A visible mismatch is therefore evidence against using that pair for the
invisibility/collision route, not a contradiction with the barrier. -/
def SourceVisibilityOrientation : Prop :=
  ∀ (M : PolyDTMCandidate)
    (x y : BitString)
    (q : Nat),
    q < SharedReadConePrefix M x y →
    q < x.length →
    q < y.length →
    x.getD q false ≠ y.getD q false →
    x.take (SharedReadConePrefix M x y) ≠
      y.take (SharedReadConePrefix M x y)

theorem sourceVisibilityOrientation_closed :
    SourceVisibilityOrientation := by
  intro M x y q hqCone hqx hqy hDiff
  exact visible_bit_mismatch_prevents_prefix_equality
    x y (SharedReadConePrefix M x y) q
    hqCone hqx hqy hDiff

/-- Thus the favorable route for sharedReadCone_invisibility is not
SOURCE_VISIBLE.  It is a pair for which every actual disagreement occurs at
or beyond the shared read-cone boundary. -/
def AllDifferencesHiddenBeyondCone
    (M : PolyDTMCandidate)
    (x y : BitString) : Prop :=
  x.take (SharedReadConePrefix M x y) =
    y.take (SharedReadConePrefix M x y)

theorem allDifferencesHidden_closes_terminalState
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (H : AllDifferencesHiddenBeyondCone M x y) :
    terminalState M x = terminalState M y :=
  sharedReadCone_invisibility M hTotal x y H

#print axioms MCore.Real.PNPDiscovery.visible_bit_mismatch_prevents_prefix_equality
#print axioms MCore.Real.PNPDiscovery.sourceVisibilityOrientation_closed
#print axioms MCore.Real.PNPDiscovery.allDifferencesHidden_closes_terminalState

end PNPDiscovery
end Real
end MCore
