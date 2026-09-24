import MCore.Real.P02EffectiveCompilerConstruction
import MCore.Real.P02FinalAttack

namespace MCore
namespace Real
namespace P02CompilerTerminalPromotion

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02EffectiveCompilerConstruction
open P02ExactCompilerSemantics
open P02FinalAttack
open P02DiagonalFrontier
open P02WitnessChain
open P02TerminalFrontier
open FinalExternalCertificate

/-- Uniform computability of compilerValue supplies the exact semantic
compiler, hence a diagonal family. -/
noncomputable theorem compilerComputable_to_D3
    (hComp : UniformCompilerValueComputable) :
    D3SemanticSelfReference := by
  have hExact : UniformExactCompilerSemantics :=
    uniformCompilerValueComputable_implies_exact hComp
  exact ⟨uniformExactCompilerSemantics_toDiagonalFamily hExact⟩

/-- Internal terminal theorem: once the single remaining compiler theorem and
the already-separated P01 producer are supplied, P != NP in the repository's
canonical internal model follows. -/
theorem compilerComputable_P01_to_internal_final
    (hComp : UniformCompilerValueComputable)
    (hP01 : SATInNPGap circuitBitEncoding) :
    PneqNP := by
  exact P01_D3_to_internal_final
    hP01
    (compilerComputable_to_D3 hComp)

/-- Assemble the complete external payload from the one remaining compiler
theorem plus the already-existing P01 and G3 producers. -/
noncomputable def compilerComputable_to_FinalExternalInputs
    (hComp : UniformCompilerValueComputable)
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FinalExternalInputs :=
  assembleFinalExternal
    hP01
    (compilerComputable_to_D3 hComp)
    hG3

/-- External terminal theorem.  No hidden hypothesis is introduced: the only
new mathematical premise is UniformCompilerValueComputable. -/
theorem compilerComputable_P01_G3_to_external_final
    (hComp : UniformCompilerValueComputable)
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FailProofAllGaps.OfficialPneqNP
      hG3.selection.model.P hG3.selection.model.NP := by
  exact P01_D3_G3_to_external_final
    hP01
    (compilerComputable_to_D3 hComp)
    hG3

/-- Packaged final-external gap consequence. -/
noncomputable theorem compilerComputable_P01_G3_to_FinalExternalGap
    (hComp : UniformCompilerValueComputable)
    (hP01 : SATInNPGap circuitBitEncoding)
    (hG3 : G3ModelMatch.G3ExternalContract) :
    FinalExternalGap :=
  ⟨compilerComputable_to_FinalExternalInputs hComp hP01 hG3⟩

#print axioms MCore.Real.P02CompilerTerminalPromotion.compilerComputable_to_D3
#print axioms MCore.Real.P02CompilerTerminalPromotion.compilerComputable_P01_to_internal_final
#print axioms MCore.Real.P02CompilerTerminalPromotion.compilerComputable_P01_G3_to_external_final
#print axioms MCore.Real.P02CompilerTerminalPromotion.compilerComputable_P01_G3_to_FinalExternalGap

end P02CompilerTerminalPromotion
end Real
end MCore
