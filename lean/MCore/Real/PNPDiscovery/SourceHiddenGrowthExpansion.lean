import MCore.Real.PNPDiscovery.SourcePrefixEndEnvelope
import MCore.Real.PNPDiscovery.SourceCellBitTransportClosed

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding

/-- Fully unfolded closed form of the source-prefix envelope. -/
theorem sourcePrefixEndEnvelope_expanded
    (D : PolyDTMCandidate)
    (n t j : Nat) :
    sourcePrefixEndEnvelope D n t j =
      let M := complementToNTMCandidate D
      let r := n + t + 1
      stateEncodingCost D +
        (3 * ((t + 1) * ntmStateCount M) + 48) +
        r *
          (3 *
            (((t + 1) * ntmStateCount M + (t + 1) * 3) +
              3 * r) + 48) +
        (j + 1) *
          (3 *
            ((((t + 1) * ntmStateCount M + (t + 1) * 3) +
              (t + 1) * r * 3) +
              3 * j) + 48) := by
  unfold sourcePrefixEndEnvelope
  unfold leftCellEncodingEnvelope rightCellEncodingEnvelope
  simp [ntmHeadBase, ntmStateSlots, ntmLeftBase,
    ntmRightBase, ntmRadius]
  ring

/-- If the concrete localized source mismatch lies outside the shared read
cone, the surviving condition is an explicit clock-vs-Cook--Levin-layout
inequality. -/
theorem hiddenSource_implies_clock_lt_envelope
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y)
    (q : Nat)
    (hLocal :
      let N := complementToNTMCandidate M
      let tx := M.timeBound x.length
      let ty := M.timeBound y.length
      let ex := sourcePrefixBitEnd N x tx (W.j + 1)
      let ey := sourcePrefixBitEnd N y ty (W.j + 1)
      q < Nat.min ex ey)
    (hHidden :
      SharedReadConePrefix M x y ≤ q) :
    Nat.min
        (M.timeBound x.length)
        (M.timeBound y.length) + 1 <
      sourcePrefixEndEnvelope
        M x.length
        (M.timeBound x.length)
        W.j := by
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hRadius :
      W.j + 1 ≤ ntmRadius x tx := W.in_radius
  have hEnd :
      sourcePrefixBitEnd N x tx (W.j + 1) ≤
        sourcePrefixEndEnvelope M x.length tx W.j :=
    sourcePrefixBitEnd_le_envelope
      M x tx W.j hRadius
  have hqEnd :
      q < sourcePrefixBitEnd N x tx (W.j + 1) := by
    dsimp [N, tx, ty] at hLocal
    omega
  unfold SharedReadConePrefix at hHidden
  dsimp [tx]
  omega

/-- Every source mismatch now has a literal bit q.  Either q is visible to
the shared cone, or the explicit polynomial-layout inequality above holds. -/
theorem sourceMismatch_visible_or_explicitGrowth
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) :
    (∃ q : Nat,
      q < SharedReadConePrefix M x y ∧
      let N := complementToNTMCandidate M
      let tx := M.timeBound x.length
      let ty := M.timeBound y.length
      let Fx := boundedExecTableauCNF_NTM N x tx
      let Fy := boundedExecTableauCNF_NTM N y ty
      (encodeCircuit (ntmCNFCircuit Fx)).getD q false ≠
        (encodeCircuit (ntmCNFCircuit Fy)).getD q false) ∨
    Nat.min
        (M.timeBound x.length)
        (M.timeBound y.length) + 1 <
      sourcePrefixEndEnvelope
        M x.length
        (M.timeBound x.length)
        W.j := by
  rcases sourceCellBitTransport_closed M x y W with
    ⟨q, hStartEq, hStart, hEnd, hDiff⟩
  rcases bitBeforeSharedCone_or_after M x y q with
    hVisible | hHidden
  · left
    exact ⟨q, hVisible, hDiff⟩
  · right
    exact hiddenSource_implies_clock_lt_envelope
      M x y W q hEnd hHidden

/-- Expanded version exposing only arithmetic primitives and candidate
constants. -/
theorem sourceMismatch_visible_or_expandedGrowth
    (M : PolyDTMCandidate)
    (x y : BitString)
    (W : SourceMismatchWitness M x y) :
    (∃ q : Nat,
      q < SharedReadConePrefix M x y ∧
      let N := complementToNTMCandidate M
      let tx := M.timeBound x.length
      let ty := M.timeBound y.length
      let Fx := boundedExecTableauCNF_NTM N x tx
      let Fy := boundedExecTableauCNF_NTM N y ty
      (encodeCircuit (ntmCNFCircuit Fx)).getD q false ≠
        (encodeCircuit (ntmCNFCircuit Fy)).getD q false) ∨
    let N := complementToNTMCandidate M
    let n := x.length
    let t := M.timeBound x.length
    let r := n + t + 1
    Nat.min
        (M.timeBound x.length)
        (M.timeBound y.length) + 1 <
      stateEncodingCost M +
        (3 * ((t + 1) * ntmStateCount N) + 48) +
        r *
          (3 *
            (((t + 1) * ntmStateCount N + (t + 1) * 3) +
              3 * r) + 48) +
        (W.j + 1) *
          (3 *
            ((((t + 1) * ntmStateCount N + (t + 1) * 3) +
              (t + 1) * r * 3) +
              3 * W.j) + 48) := by
  rcases sourceMismatch_visible_or_explicitGrowth M x y W with
    hVisible | hGrowth
  · exact Or.inl hVisible
  · right
    dsimp
    rw [← sourcePrefixEndEnvelope_expanded
      M x.length (M.timeBound x.length) W.j]
    exact hGrowth

#print axioms MCore.Real.PNPDiscovery.sourcePrefixEndEnvelope_expanded
#print axioms MCore.Real.PNPDiscovery.hiddenSource_implies_clock_lt_envelope
#print axioms MCore.Real.PNPDiscovery.sourceMismatch_visible_or_explicitGrowth
#print axioms MCore.Real.PNPDiscovery.sourceMismatch_visible_or_expandedGrowth

end PNPDiscovery
end Real
end MCore
