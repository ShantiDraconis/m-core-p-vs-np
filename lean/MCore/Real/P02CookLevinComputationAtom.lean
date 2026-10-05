import MCore.Real.P02EqualityBranchMaterialFrontier

namespace MCore
namespace Real
namespace P02CookLevinComputationAtom

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

/-- Exact operational obligation for atom 1. No endpoint or P/NP proposition
is stored here: only a universal physical polynomial-time reduction producer. -/
def COOK_LEVIN_COMPUTATION_OPEN_MATH : Prop :=
  Nonempty UniversalCookLevinMaterializer

/-- Pointwise constructor target: for one NP realization, provide semantic
reduction, output-size polynomial, and a DTM physically computing that output. -/
structure CookLevinInstanceProducer
    {L : BitLanguage}
    (R : PolyNTMRealization L) where
  semantic : SemanticReduction R
  size : ReductionSizePolynomial semantic
  computation : ReductionComputationCertificate semantic

def CookLevinInstanceProducer.toMaterial
    {L : BitLanguage}
    {R : PolyNTMRealization L}
    (P : CookLevinInstanceProducer R) :
    CookLevinMaterial R :=
  { semantic := P.semantic
    size := P.size
    computation := P.computation }

/-- A uniform pointwise producer is exactly enough to inhabit atom 1. -/
def universalCookLevin_of_instanceProducer
    (P :
      ∀ {L : BitLanguage} (R : PolyNTMRealization L),
        CookLevinInstanceProducer R) :
    UniversalCookLevinMaterializer where
  material := fun R => (P R).toMaterial

/-- The actual machine-level leaf for one fixed semantic reduction. -/
def PHYSICAL_REDUCTION_LEAF
    {L : BitLanguage}
    {R : PolyNTMRealization L}
    (S : SemanticReduction R) : Prop :=
  Nonempty (ReductionComputationCertificate S)

#print axioms MCore.Real.P02CookLevinComputationAtom.CookLevinInstanceProducer.toMaterial
#print axioms MCore.Real.P02CookLevinComputationAtom.universalCookLevin_of_instanceProducer

end P02CookLevinComputationAtom
end Real
end MCore
