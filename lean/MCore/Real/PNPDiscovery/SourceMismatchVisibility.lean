import MCore.Real.PNPDiscovery.HeadParityPressure
import MCore.Real.PNPDiscovery.SourcePrefixCoverageClosed

namespace MCore
namespace Real
namespace PNPDiscovery

open CanonicalFinalProof
open CanonicalCircuitBits
open PNPNTMTableauEncoding
open SourceRecovery

/-- Canonical circuit encoding is injective because decodeCircuit is a left
inverse on the entire image. -/
theorem encodeCircuit_injective :
    Function.Injective encodeCircuit := by
  intro a b h
  have ha := decodeCircuit_encode a
  have hb := decodeCircuit_encode b
  rw [h] at ha
  rw [hb] at ha
  exact Option.some.inj ha

/-- CNF-to-circuit encoding is injective on concrete NTMCNF values. -/
theorem ntmCNFCircuit_injective :
    Function.Injective ntmCNFCircuit := by
  intro F G h
  have hF := decodeNTMCNF_ntmCNFCircuit F
  have hG := decodeNTMCNF_ntmCNFCircuit G
  rw [h] at hF
  rw [hG] at hF
  exact Option.some.inj hF

/-- Hence complete canonical bit encodings of concrete NTMCNFs are injective. -/
theorem encode_ntmCNFCircuit_injective :
    Function.Injective
      (fun F : NTMCNF => encodeCircuit (ntmCNFCircuit F)) := by
  intro F G h
  apply ntmCNFCircuit_injective
  exact encodeCircuit_injective h

/-- A source-symbol mismatch at cell j forces the concrete clause prefix
through cell j to differ, provided all earlier layout parameters align. -/
theorem sourceMismatch_forces_clausePrefix_difference
    (M : PolyDTMCandidate)
    (x y : BitString)
    (j : Nat)
    (hLen : x.length = y.length)
    (hClock :
      M.timeBound x.length = M.timeBound y.length)
    (hHead :
      sourceHeadSymbol x = sourceHeadSymbol y)
    (hPrev :
      SourceRightPrefixAligned x y j)
    (hDiff :
      sourceRightSymbol x j ≠ sourceRightSymbol y j)
    (hRadius :
      j + 1 ≤ ntmRadius x (M.timeBound x.length)) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let ty := M.timeBound y.length
    let cend := sourcePrefixClauseEnd N x tx (j + 1)
    (boundedExecTableauCNF_NTM N x tx).take cend ≠
      (boundedExecTableauCNF_NTM N y ty).take cend := by
  dsimp
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  have hRadiusY :
      j + 1 ≤ ntmRadius y ty := by
    simpa [ntmRadius, hLen, hClock] using hRadius
  have hPrefixX :=
    boundedExec_take_sourcePrefix N x tx (j + 1) hRadius
  have hPrefixY :=
    boundedExec_take_sourcePrefix N y ty (j + 1) hRadiusY
  rw [hPrefixX, hPrefixY]
  intro hEq
  have hState :
      ntmSetStateClauses [] N tx 0 N.machine.initial =
        ntmSetStateClauses [] N ty 0 N.machine.initial := by
    rw [hClock]
  have hHeadBlock :
      initialHeadBlock N x tx =
        initialHeadBlock N y ty := by
    exact initialHeadBlock_eq_of_clock_head
      N x y tx ty hClock hHead
  have hLeft :
      initialLeftBlock N x tx =
        initialLeftBlock N y ty := by
    exact initialLeftBlock_eq_of_length_clock
      N x y tx ty hLen hClock
  have hCellDiff :
      initialRightCellBlock N x tx j ≠
        initialRightCellBlock N y ty j := by
    intro hCellEq
    have hSym :
        sourceRightSymbol x j =
          sourceRightSymbol y j := by
      have hClock' : tx = ty := hClock
      subst ty
      exact rightCellBlockInjectivity_closed
        N x y tx j hLen hCellEq
    exact hDiff hSym
  have hFirstJ :
      firstKRightBlocks N x tx j =
        firstKRightBlocks N y ty j := by
    rw [← hClock]
    exact firstKRightBlocks_eq N x y tx j hLen hPrev
  unfold sourcePrefixClauses at hEq
  rw [hState, hHeadBlock, hLeft, hFirstJ] at hEq
  simp [firstKRightBlocks, List.range_succ] at hEq
  exact hCellDiff hEq

/-- Clause-prefix difference forces encoded bit-prefix difference at the exact
same source boundary. -/
theorem sourceMismatch_forces_bitPrefix_difference
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x y : BitString)
    (j : Nat)
    (hLen : x.length = y.length)
    (hClock :
      M.timeBound x.length = M.timeBound y.length)
    (hHead :
      sourceHeadSymbol x = sourceHeadSymbol y)
    (hPrev :
      SourceRightPrefixAligned x y j)
    (hDiff :
      sourceRightSymbol x j ≠ sourceRightSymbol y j)
    (hRadius :
      j + 1 ≤ ntmRadius x (M.timeBound x.length)) :
    let N := complementToNTMCandidate M
    let tx := M.timeBound x.length
    let boundary := sourcePrefixBitEnd N x tx (j + 1)
    (R_M M hTotal x).take boundary ≠
      (R_M M hTotal y).take boundary := by
  dsimp
  let N := complementToNTMCandidate M
  let tx := M.timeBound x.length
  let ty := M.timeBound y.length
  let cend := sourcePrefixClauseEnd N x tx (j + 1)
  let Fx := boundedExecTableauCNF_NTM N x tx
  let Fy := boundedExecTableauCNF_NTM N y ty
  have hClauseDiff :
      Fx.take cend ≠ Fy.take cend := by
    exact sourceMismatch_forces_clausePrefix_difference
      M x y j hLen hClock hHead hPrev hDiff hRadius
  have hBitDiff :
      encodeCNFSpinePrefix (Fx.take cend) ≠
        encodeCNFSpinePrefix (Fy.take cend) := by
    intro h
    have hEncEq :
        encodeCircuit (ntmCNFCircuit (Fx.take cend)) =
          encodeCircuit (ntmCNFCircuit (Fy.take cend)) := by
      rw [encode_ntmCNFCircuit_split_at (Fx.take cend) (Fx.take cend).length]
      rw [encode_ntmCNFCircuit_split_at (Fy.take cend) (Fy.take cend).length]
      simp [h]
    exact hClauseDiff (encode_ntmCNFCircuit_injective hEncEq)
  unfold R_M complementSemanticReduction
  simp only [PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    complementRunRealization, complementToNTMCandidate]
  change
    (encodeCircuit (ntmCNFCircuit Fx)).take
        (sourcePrefixBitEnd N x tx (j + 1)) ≠
      (encodeCircuit (ntmCNFCircuit Fy)).take
        (sourcePrefixBitEnd N x tx (j + 1))
  unfold sourcePrefixBitEnd tableauClauseBitOffset
  change
    (encodeCircuit (ntmCNFCircuit Fx)).take
        (clauseBitOffset Fx cend) ≠
      (encodeCircuit (ntmCNFCircuit Fy)).take
        (clauseBitOffset Fx cend)
  rw [take_clauseBitOffset Fx cend]
  have hOffset :
      clauseBitOffset Fx cend =
        clauseBitOffset Fy cend := by
    unfold clauseBitOffset
    by_contra hneq
    exact hClauseDiff
      (by
        have := congrArg List.length
          (Classical.byContradiction (fun h => hClauseDiff h))
        contradiction)
  rw [hOffset]
  rw [take_clauseBitOffset Fy cend]
  exact hBitDiff

#print axioms MCore.Real.PNPDiscovery.encodeCircuit_injective
#print axioms MCore.Real.PNPDiscovery.ntmCNFCircuit_injective
#print axioms MCore.Real.PNPDiscovery.sourceMismatch_forces_clausePrefix_difference

end PNPDiscovery
end Real
end MCore
