import MCore.Real.PNPDiscovery.ExactOpenMathMinCut
import MCore.Real.PNPDiscovery.PlusOneSemanticsAudit
import MCore.Real.PNPDiscovery.CanonicalClockNormalization
import MCore.Real.PNPDiscovery.FiniteCandidateDescription
import MCore.Real.PNPDiscovery.UnaryListSerialization
import MCore.Real.PNPDiscovery.ConcreteMachineInputPairing
import MCore.Real.PNPDiscovery.SourceCellBitTransportClosed

namespace MCore
namespace Real
namespace PNPDiscovery
namespace KernelTestClosedLayer

open CanonicalFinalProof
open P02ExactDiagonalFrontier

/-- Kernel regression: the exact material endpoint wiring is closed. -/
example (hNP : SATInNPPhysicalGap)
    (hSep : TotalExactDiagonalProducer) :
    PneqNP :=
  exactMaterialMinCut_closes
    { satInNP := hNP, separation := hSep }

/-- Kernel regression: separation-side frontier is exactly universal failure. -/
example :
    TotalExactDiagonalProducer ↔ SATSeparationGap :=
  exactSeparationOpenAtom_iff_endpoint

/-- Kernel regression: total candidate clock normalization preserves semantics. -/
example (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M)
    (x : BitString) :
    DeclaredAccepts (canonicalClockCandidate M) x ↔
      DeclaredAccepts M x :=
  canonicalClock_declaredAccepts_iff M hTotal x

/-- Kernel regression: finite normalized descriptions preserve total-candidate semantics. -/
example (M : PolyDTMCandidate)
    (hTotal : P02TotalCandidateKleeneReduction.DeclaredClockTotal M)
    (x : BitString) :
    DeclaredAccepts ((finiteDescription M).toCandidate) x ↔
      DeclaredAccepts M x :=
  finiteDescription_semantic_roundTrip_closed M hTotal x

/-- Kernel regression: unary list serialization round-trips. -/
example (xs : List Nat) :
    decodeNatList (encodeNatList xs) = some (xs, []) :=
  decodeNatList_encode xs

/-- Kernel regression: code/input pairing round-trips. -/
example (code x : BitString) :
    concreteUnpack (concretePack code x) = some (code, x) :=
  concreteUnpack_pack code x

/-- Kernel regression: all structural +1 meanings remain theorem-backed. -/
example (x y : BitString) (t u : Nat)
    (h : PNPNTMTableauEncoding.ntmRadius x t =
      PNPNTMTableauEncoding.ntmRadius y u) :
    x.length + t = y.length + u :=
  equalRadius_cancels_plusOne x y t u h

#print axioms MCore.Real.PNPDiscovery.exactMaterialMinCut_closes
#print axioms MCore.Real.PNPDiscovery.canonicalClock_declaredAccepts_iff
#print axioms MCore.Real.PNPDiscovery.finiteDescription_semantic_roundTrip_closed
#print axioms MCore.Real.PNPDiscovery.decodeNatList_encode
#print axioms MCore.Real.PNPDiscovery.concreteUnpack_pack

end KernelTestClosedLayer
end PNPDiscovery
end Real
end MCore
