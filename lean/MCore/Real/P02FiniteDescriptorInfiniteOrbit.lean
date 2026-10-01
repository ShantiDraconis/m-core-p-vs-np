import MCore.Real.P02OpenMathRouteFalsification
import MCore.Real.P02FiniteDescriptorAlternation

namespace MCore
namespace Real
namespace P02FiniteDescriptorInfiniteOrbit

open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02OpenMathRouteFalsification
open P02ComplementTableauDiagonal
open P02DiagonalOrbitCore
open P02FiniteDescriptorReduction
open P02FiniteDescriptorOrbitResidual
open P02FiniteDescriptorAlternation

/-- The canonical complement-tableau diagonal transform strictly increases
bitstring length.  This is a structural fact about the current encoding. -/
theorem diagonalBits_strict_growth
    (M : PolyDTMCandidate)
    (x : BitString) :
    x.length < (diagonalBits M x).length := by
  let t := M.timeBound x.length
  have hcnf :
      x.length <
        (boundedExecTableauCNF
          (P02ComplementTableauDiagonal.complementCandidate M) x t).length :=
    boundedExecTableauCNF_length_gt_input
      (P02ComplementTableauDiagonal.complementCandidate M) x t
  have henc :
      (boundedExecTableauCNF
        (P02ComplementTableauDiagonal.complementCandidate M) x t).length ≤
      (encodeCircuit
        (cnfCircuit
          (boundedExecTableauCNF
            (P02ComplementTableauDiagonal.complementCandidate M) x t))).length :=
    cnfCircuit_encode_length_ge_clause_count _
  unfold diagonalBits boundedExecBits boundedExecCircuit
  exact Nat.lt_of_lt_of_le hcnf henc

theorem orbit_length_step
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    (orbit M seed n).length <
      (orbit M seed (n + 1)).length := by
  simpa [orbit] using
    diagonalBits_strict_growth M (orbit M seed n)

/-- Orbit lengths are strictly monotone. -/
theorem orbit_length_strictMono
    (M : PolyDTMCandidate)
    (seed : BitString) :
    StrictMono (fun n => (orbit M seed n).length) := by
  exact strictMono_nat_of_lt_succ
    (fun n => orbit_length_step M seed n)

/-- Hence the diagonal orbit contains no repeated bitstring. -/
theorem orbit_injective
    (M : PolyDTMCandidate)
    (seed : BitString) :
    Function.Injective (orbit M seed) := by
  intro i j hij
  have hlen :
      (orbit M seed i).length =
        (orbit M seed j).length :=
    congrArg List.length hij
  exact (orbit_length_strictMono M seed).injective hlen

theorem orbit_ne_next
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    orbit M seed n ≠ orbit M seed (n + 1) := by
  intro h
  exact Nat.ne_of_lt (orbit_length_step M seed n)
    (congrArg List.length h)

/-- Surviving residual descriptors therefore carry two infinite injective
diagonal orbits, and correctness on them forces exact Boolean alternation. -/
structure InfiniteAlternatingOrbitCertificate
    (D : FiniteDTMDescriptor) : Prop where
  false_injective :
    Function.Injective (orbit D.toCandidate falseBits)
  true_injective :
    Function.Injective (orbit D.toCandidate trueBits)
  false_alternates :
    AlternatingOrbit D.toCandidate falseBits
  true_alternates :
    AlternatingOrbit D.toCandidate trueBits

theorem infinite_alternating_certificate
    (D : FiniteDTMDescriptor)
    (hOrbit : DescriptorOrbitCorrect D) :
    InfiniteAlternatingOrbitCertificate D := by
  have hAlt :=
    residual_descriptor_has_two_alternating_orbits D hOrbit
  exact
    { false_injective := orbit_injective D.toCandidate falseBits
      true_injective := orbit_injective D.toCandidate trueBits
      false_alternates := hAlt.1
      true_alternates := hAlt.2 }

#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.diagonalBits_strict_growth
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_length_strictMono
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.orbit_injective
#print axioms MCore.Real.P02FiniteDescriptorInfiniteOrbit.infinite_alternating_certificate

end P02FiniteDescriptorInfiniteOrbit
end Real
end MCore
