import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01IntegratedAssembly
import MCore.Real.P01CheckedVerifierStateCodec

namespace MCore
namespace Real
namespace P01CheckedVerifierFiniteState

open P01IntegratedAssembly
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierStateCodec

/-- Exact number expected by P01MachineConstruction: the concrete verifier
has 1852 reachable control values, represented as Fin (1851 + 1). -/
def checkedVerifierStateCount : Nat := 1851

def checkedVerifierStateEncode
    (q : CheckedVerifierState) :
    Fin (checkedVerifierStateCount + 1) :=
  ⟨(checkedVerifierStateCodec.encode q).val, by
    have h := (checkedVerifierStateCodec.encode q).isLt
    rw [checkedVerifierStateCodec_size] at h
    simpa [checkedVerifierStateCount] using h⟩

def checkedVerifierStateDecode
    (q : Fin (checkedVerifierStateCount + 1)) :
    CheckedVerifierState :=
  checkedVerifierStateCodec.decode
    ⟨q.val, by
      have h := q.isLt
      rw [checkedVerifierStateCodec_size]
      simpa [checkedVerifierStateCount] using h⟩

theorem checkedVerifierStateDecode_encode
    (q : CheckedVerifierState) :
    checkedVerifierStateDecode (checkedVerifierStateEncode q) = q := by
  unfold checkedVerifierStateDecode checkedVerifierStateEncode
  simpa using checkedVerifierStateCodec.decode_encode q

/-- Concrete Fin-indexed checked verifier obtained only by control-state
relabeling. No transition, tape, acceptance or rejection semantics changes. -/
def checkedVerifierFinMachine :
    NTM (Fin (checkedVerifierStateCount + 1)) (Option Bool) :=
  P01IntegratedAssembly.relabel
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode

@[simp] theorem checkedVerifierFinMachine_blank :
    checkedVerifierFinMachine.blank = none := rfl

theorem checkedVerifierFinMachine_haltsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.HaltsWithin n
        (P01NTMRunLaws.liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.HaltsWithin n c := by
  exact P01IntegratedAssembly.relabel_haltsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

theorem checkedVerifierFinMachine_acceptsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.AcceptsWithin n
        (P01NTMRunLaws.liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.AcceptsWithin n c := by
  exact P01IntegratedAssembly.relabel_acceptsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierStateDecode_encode
#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierFinMachine_haltsWithin_iff
#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierFinMachine_acceptsWithin_iff

end P01CheckedVerifierFiniteState
end Real
end MCore
