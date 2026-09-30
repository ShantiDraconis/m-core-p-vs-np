import MCore.Real.P01ManualStateCodecComposite
import MCore.Real.P01IntegratedAssembly

namespace MCore
namespace Real
namespace P01ManualCheckedVerifierFiniteState

open P01ManualStateCodecComposite
open P01CheckedVerifierCompositeNTM
open P01IntegratedAssembly
open P01NTMRunLaws

/-! Final explicit codec for CheckedVerifierState. -/

def fin2Code (q : Fin 2) : Nat := q.val

def fin2Decode (n : Nat) : Fin 2 :=
  if h : n < 2 then ⟨n, h⟩ else 0

@[simp] theorem fin2Decode_code (q : Fin 2) :
    fin2Decode (fin2Code q) = q := by
  apply Fin.ext
  simp [fin2Decode, fin2Code, q.isLt]

theorem fin2Code_lt (q : Fin 2) :
    fin2Code q < 2 := q.isLt

def checkedVerifierStateCount : Nat := 1852

def checkedVerifierCode : CheckedVerifierState → Nat
  | .start => 0
  | .scan q => 1 + fin2Code q
  | .enter => 3
  | .eval q => 4 + checkedEvalCode q
  | .reject => 1851

def checkedVerifierDecodeNat (n : Nat) : CheckedVerifierState :=
  if n = 0 then .start
  else if n < 3 then .scan (fin2Decode (n - 1))
  else if n = 3 then .enter
  else if n < 1851 then .eval (checkedEvalDecode (n - 4))
  else .reject

@[simp] theorem checkedVerifierDecodeNat_code
    (q : CheckedVerifierState) :
    checkedVerifierDecodeNat (checkedVerifierCode q) = q := by
  cases q with
  | start =>
      simp [checkedVerifierDecodeNat, checkedVerifierCode]
  | scan q =>
      have h := fin2Code_lt q
      simp [checkedVerifierDecodeNat, checkedVerifierCode, h, fin2Decode_code] <;> omega
  | enter =>
      simp [checkedVerifierDecodeNat, checkedVerifierCode]
  | eval q =>
      have h := checkedEvalCode_lt q
      simp [checkedVerifierDecodeNat, checkedVerifierCode,
        checkedEvalStateCount, h, checkedEvalDecode_code] <;> omega
  | reject =>
      simp [checkedVerifierDecodeNat, checkedVerifierCode]

theorem checkedVerifierCode_lt
    (q : CheckedVerifierState) :
    checkedVerifierCode q < checkedVerifierStateCount := by
  cases q with
  | start => decide
  | scan q =>
      have h := fin2Code_lt q
      simp [checkedVerifierCode, checkedVerifierStateCount]
      omega
  | enter => decide
  | eval q =>
      have h := checkedEvalCode_lt q
      simp [checkedVerifierCode, checkedVerifierStateCount,
        checkedEvalStateCount] at *
      omega
  | reject => decide

def checkedVerifierStateEncode
    (q : CheckedVerifierState) :
    Fin (checkedVerifierStateCount + 1) :=
  ⟨checkedVerifierCode q, by
    have h := checkedVerifierCode_lt q
    simp [checkedVerifierStateCount] at h ⊢
    omega⟩

def checkedVerifierStateDecode
    (q : Fin (checkedVerifierStateCount + 1)) :
    CheckedVerifierState :=
  checkedVerifierDecodeNat q.val

@[simp] theorem checkedVerifierStateDecode_encode
    (q : CheckedVerifierState) :
    checkedVerifierStateDecode (checkedVerifierStateEncode q) = q := by
  change checkedVerifierDecodeNat (checkedVerifierCode q) = q
  exact checkedVerifierDecodeNat_code q

/-- Pure state relabelling of the already-defined checked verifier. -/
def checkedVerifierFinMachine :
    NTM (Fin (checkedVerifierStateCount + 1)) (Option Bool) :=
  relabel
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode

@[simp] theorem checkedVerifierFinMachine_blank :
    checkedVerifierFinMachine.blank = none := rfl

theorem checkedVerifierFinMachine_haltsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.HaltsWithin n
        (liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.HaltsWithin n c := by
  exact relabel_haltsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

theorem checkedVerifierFinMachine_acceptsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.AcceptsWithin n
        (liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.AcceptsWithin n c := by
  exact relabel_acceptsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

#print axioms MCore.Real.P01ManualCheckedVerifierFiniteState.fin2Decode_code
#print axioms MCore.Real.P01ManualCheckedVerifierFiniteState.checkedVerifierDecodeNat_code
#print axioms MCore.Real.P01ManualCheckedVerifierFiniteState.checkedVerifierStateDecode_encode
#print axioms MCore.Real.P01ManualCheckedVerifierFiniteState.checkedVerifierFinMachine_haltsWithin_iff
#print axioms MCore.Real.P01ManualCheckedVerifierFiniteState.checkedVerifierFinMachine_acceptsWithin_iff

end P01ManualCheckedVerifierFiniteState
end Real
end MCore
