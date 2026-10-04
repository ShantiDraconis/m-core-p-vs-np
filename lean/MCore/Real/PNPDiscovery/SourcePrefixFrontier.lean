import MCore.Real.PNPDiscovery.SourceBlockFrontier

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P02ComplementRunRealization

/-- Agreement of the first k physical source/right symbols. -/
def SourceRightPrefixAligned
    (x y : BitString)
    (k : Nat) : Prop :=
  ∀ i : Nat, i < k →
    sourceRightSymbol x i =
      sourceRightSymbol y i

theorem sourceRightPrefixAligned_zero
    (x y : BitString) :
    SourceRightPrefixAligned x y 0 := by
  intro i hi
  omega

theorem sourceRightPrefixAligned_mono
    (x y : BitString)
    {j k : Nat}
    (hjk : j ≤ k)
    (H : SourceRightPrefixAligned x y k) :
    SourceRightPrefixAligned x y j := by
  intro i hi
  exact H i (lt_of_lt_of_le hi hjk)

/-- Exact CNF prefix consisting of the first k time-zero right/source cells. -/
def initialRightPrefixCNF
    (M : PolyNTMCandidate)
    (x : BitString)
    (t k : Nat) : NTMCNF :=
  (List.range k).flatMap fun i =>
    initialRightCellBlock M x t i

/-- Prefix source alignment plus layout alignment makes the corresponding CNF
prefix literally identical. -/
theorem initialRightPrefixCNF_eq
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t u k : Nat)
    (hLen : x.length = y.length)
    (hClock : t = u)
    (hPrefix : SourceRightPrefixAligned x y k) :
    initialRightPrefixCNF M x t k =
      initialRightPrefixCNF M y u k := by
  subst u
  unfold initialRightPrefixCNF
  apply List.flatMap_congr_left
  intro i hi
  have hik : i < k := by
    simpa using (List.mem_range.mp hi)
  exact initialRightCellBlock_eq
    M x y t t i hLen rfl (hPrefix i hik)

/-- Failure of physical source-prefix alignment exposes a concrete source-cell
index below k. -/
theorem not_sourceRightPrefixAligned_exists
    (x y : BitString)
    (k : Nat)
    (H : ¬ SourceRightPrefixAligned x y k) :
    ∃ i : Nat, i < k ∧
      sourceRightSymbol x i ≠
        sourceRightSymbol y i := by
  classical
  unfold SourceRightPrefixAligned at H
  push_neg at H
  exact H

/-- First source prefix length at which alignment fails. -/
structure SourcePrefixBreak
    (x y : BitString) where
  k : Nat
  aligned_before :
    SourceRightPrefixAligned x y k
  differs_after :
    ¬ SourceRightPrefixAligned x y (k + 1)

/-- A source-prefix break gives a concrete mismatching source cell at the
extension boundary. -/
theorem sourcePrefixBreak_has_difference
    (x y : BitString)
    (B : SourcePrefixBreak x y) :
    ∃ i : Nat, i < B.k + 1 ∧
      sourceRightSymbol x i ≠
        sourceRightSymbol y i := by
  exact not_sourceRightPrefixAligned_exists
    x y (B.k + 1) B.differs_after

/-- Because all cells below k agree, the witness from a first extension break
cannot lie below k; hence it is exactly cell k. -/
theorem sourcePrefixBreak_at_boundary
    (x y : BitString)
    (B : SourcePrefixBreak x y) :
    sourceRightSymbol x B.k ≠
      sourceRightSymbol y B.k := by
  rcases sourcePrefixBreak_has_difference x y B with
    ⟨i, hi, hDiff⟩
  have hnotlt : ¬ i < B.k := by
    intro hik
    exact hDiff (B.aligned_before i hik)
  have hieq : i = B.k := by
    omega
  simpa [hieq] using hDiff

/-- Once length and clock agree, a first source-prefix break is transported
verbatim to a first differing encoded right-cell block. -/
theorem sourcePrefixBreak_gives_block_difference
    (M : PolyNTMCandidate)
    (x y : BitString)
    (t : Nat)
    (hLen : x.length = y.length)
    (B : SourcePrefixBreak x y) :
    initialRightCellBlock M x t B.k ≠
      initialRightCellBlock M y t B.k := by
  intro hEq
  have hSource :
      sourceRightSymbol x B.k =
        sourceRightSymbol y B.k := by
    by_contra h
    exact h
      (aligned_rightCell_difference_implies_source_difference
        M x y t B.k hLen hEq)
  exact (sourcePrefixBreak_at_boundary x y B) hSource

/-- Source-side discovery state for an odd pair. -/
structure OddSourceAlignment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  seed : BitString
  i : Nat
  d : Nat
  k : Nat
  let x := orbit M hTotal seed (i + 1)
  let y := orbit M hTotal seed ((i + 1) + (2 * d + 1))
  length_eq : x.length = y.length
  clock_eq :
    M.timeBound x.length = M.timeBound y.length
  head_eq :
    sourceHeadSymbol x = sourceHeadSymbol y
  source_prefix :
    SourceRightPrefixAligned x y k

/-- Exact next source-side target: grow k until the encoded stable prefix
covers the shared read cone.  No endpoint language occurs in this type. -/
def SourceAlignmentGrowthGap : Prop :=
  ∀ M : PolyDTMCandidate, ∀ hTotal : DeclaredClockTotal M,
    ∃ W : OddSourceAlignment M hTotal,
      W.k > 0

#print axioms MCore.Real.PNPDiscovery.initialRightPrefixCNF_eq
#print axioms MCore.Real.PNPDiscovery.not_sourceRightPrefixAligned_exists
#print axioms MCore.Real.PNPDiscovery.sourcePrefixBreak_at_boundary
#print axioms MCore.Real.PNPDiscovery.sourcePrefixBreak_gives_block_difference

end PNPDiscovery
end Real
end MCore
