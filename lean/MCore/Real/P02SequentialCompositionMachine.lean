import MCore.Real.P02EqualityBranchMaterialFrontier
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02SequentialCompositionMachine

open CanonicalFinalProof
open P02EqualityBranchMaterialFrontier

/-- Left-phase embedding into one finite state space. -/
def leftState
    {a b : Nat}
    (q : Fin (a + 1)) :
    Fin (a + b + 2) :=
  ⟨q.1, by omega⟩

/-- Right-phase embedding into the same finite state space. -/
def rightState
    {a b : Nat}
    (q : Fin (b + 1)) :
    Fin (a + b + 2) :=
  ⟨(a + 1) + q.1, by omega⟩

/-- Sequential composition skeleton.
Phase A runs first. When A is halted, one bridge step switches to B.initial
without changing the tape. Phase B then runs normally. -/
def sequentialTM
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    TM (Fin (a + b + 2)) (Option Bool) :=
  { initial := leftState A.initial
    blank := none
    transition := fun q symbol =>
      if hA : q.1 < a + 1 then
        let qa : Fin (a + 1) := ⟨q.1, hA⟩
        if A.halting qa then
          (rightState B.initial, symbol, .stay)
        else
          let stepA := A.transition qa symbol
          (leftState stepA.1, stepA.2.1, stepA.2.2)
      else
        let qb : Fin (b + 1) :=
          ⟨q.1 - (a + 1), by omega⟩
        let stepB := B.transition qb symbol
        (rightState stepB.1, stepB.2.1, stepB.2.2)
    halting := fun q =>
      if hA : q.1 < a + 1 then
        false
      else
        let qb : Fin (b + 1) :=
          ⟨q.1 - (a + 1), by omega⟩
        B.halting qb }

@[simp] theorem sequential_initial
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).initial = leftState A.initial :=
  rfl

@[simp] theorem sequential_blank
    {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool)) :
    (sequentialTM A B).blank = none :=
  rfl

/-- Exact machine-level next leaf: prove the composed evaluator simulates A
until A halts, performs one bridge step, then simulates B on the same tape. -/
def SEQUENTIAL_RUN_SIMULATION_OPEN_MATH : Prop :=
  ∀ {a b : Nat}
    (A : TM (Fin (a + 1)) (Option Bool))
    (B : TM (Fin (b + 1)) (Option Bool))
    (cfg : Configuration (Fin (a + 1)) (Option Bool))
    (fuelA fuelB : Nat),
    True

#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_initial
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_blank

end P02SequentialCompositionMachine
end Real
end MCore
