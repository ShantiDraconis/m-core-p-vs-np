import MCore.Real.CanonicalSATParserTerminalBranches

namespace MCore
namespace Real
namespace CanonicalSATParserTerminalCases

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserLeafReturnProof
open CanonicalSATParserLeafSourceProof
open CanonicalSATParserReturnProof
open CanonicalSATParserTerminalBranches

/-- Reuse the already-certified residual-source rejection theorem. -/
theorem leaf16_nonempty_rejects
    (pad : Nat)
    (last : Bool)
    (rest : BitString)
    (right : List (Option Bool)) :
    parserMachine.step
        (leafSourceCheckConfig 16
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          right) =
      leafResidualRejectConfig pad last rest right :=
  leaf16_residual_rejects pad last rest right

/-- Reuse the already-certified exhausted-binary rejection theorem. -/
theorem binary_check_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (right : List (Option Bool)) :
    parserMachine.run 2
        (binaryReturnConfig []
          (List.replicate pad (none : Option Bool))
          right) =
      leafRejectConfig pad right :=
  binary_exhausted_rejects pad hpad right

#print axioms MCore.Real.CanonicalSATParserTerminalCases.leaf16_nonempty_rejects
#print axioms MCore.Real.CanonicalSATParserTerminalCases.binary_check_exhausted_rejects

end CanonicalSATParserTerminalCases
end Real
end MCore
