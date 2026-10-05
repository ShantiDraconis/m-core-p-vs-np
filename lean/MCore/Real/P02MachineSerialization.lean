import MCore.Real.P02FiniteMachineDescription
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02MachineSerialization

open CanonicalFinalProof
open CanonicalCircuitBits
open P02FiniteMachineDescription

structure TransitionEntry where
  next : Nat
  write : Option Bool
  move : Direction
  deriving Repr, DecidableEq

structure MachinePayload where
  stateCount : Nat
  initial : Nat
  transitions : List TransitionEntry
  halting : List Bool
  accepting : List Bool
  deriving Repr, DecidableEq

def symbolIndex : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2

def symbolOfIndex : Nat → Option Bool
  | 0 => none
  | 1 => some false
  | _ => some true

def transitionEntry
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1))
    (s : Option Bool) : TransitionEntry :=
  let t := enc.transition q s
  { next := t.1.val
    write := t.2.1
    move := t.2.2 }

def machinePayload (enc : EncodedMachine) : MachinePayload :=
  { stateCount := enc.stateCount
    initial := enc.initial.val
    transitions :=
      (List.ofFn fun q : Fin (enc.stateCount + 1) =>
        [ transitionEntry enc q none
        , transitionEntry enc q (some false)
        , transitionEntry enc q (some true) ]).flatten
    halting := List.ofFn enc.halting
    accepting := List.ofFn enc.accepting }

def payloadTransitionIndex (q : Nat) (s : Option Bool) : Nat :=
  3 * q + symbolIndex s

def transitionDefault : TransitionEntry :=
  { next := 0, write := none, move := .stay }

def payloadToMachine (p : MachinePayload) : EncodedMachine :=
  let n := p.stateCount
  { stateCount := n
    initial := ⟨p.initial % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    transition := fun q s =>
      let e := p.transitions.getD (payloadTransitionIndex q.val s) transitionDefault
      let q' : Fin (n + 1) :=
        ⟨e.next % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
      (q', e.write, e.move)
    halting := fun q => p.halting.getD q.val false
    accepting := fun q => p.accepting.getD q.val false }

theorem list_ofFn_getD
    {n : Nat} {α : Type}
    (f : Fin n → α)
    (i : Fin n)
    (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_ofFn, i.isLt]

theorem payload_halting_roundtrip
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1)) :
    (payloadToMachine (machinePayload enc)).halting q = enc.halting q := by
  change (List.ofFn enc.halting).getD q.val false = enc.halting q
  exact list_ofFn_getD enc.halting q false

theorem payload_accepting_roundtrip
    (enc : EncodedMachine)
    (q : Fin (enc.stateCount + 1)) :
    (payloadToMachine (machinePayload enc)).accepting q = enc.accepting q := by
  change (List.ofFn enc.accepting).getD q.val false = enc.accepting q
  exact list_ofFn_getD enc.accepting q false

#print axioms MCore.Real.P02MachineSerialization.list_ofFn_getD
#print axioms MCore.Real.P02MachineSerialization.payload_halting_roundtrip
#print axioms MCore.Real.P02MachineSerialization.payload_accepting_roundtrip

end P02MachineSerialization
end Real
end MCore
