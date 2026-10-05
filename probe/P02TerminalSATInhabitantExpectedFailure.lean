import MCore.Real.P02TerminalForcingSAT

namespace MCore
namespace Real
namespace P02TerminalInhabitantProbeSAT

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier
open P02TerminalForcingSAT

/-
DIRECT TERMINAL ATTACK.
No InP CanonicalSAT hypothesis, oracle, axiom, sorry or wrapper is supplied.
Lean must synthesize an actual SATSolverData inhabitant.
-/
example : SAT_SOLVER_TERMINAL := by
  unfold SAT_SOLVER_TERMINAL
  refine ⟨{
    stateCount := ?_
    machine := ?_
    blank_none := ?_
    accepting := ?_
    timeBound := ?_
    time_poly := ?_
    halts := ?_
    correct := ?_ }⟩

end P02TerminalInhabitantProbeSAT
end Real
end MCore
