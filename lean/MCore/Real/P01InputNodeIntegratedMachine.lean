import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01EvalInputNodePhysicalRefinement
import MCore.Real.P01InputAfterReadReturn

namespace MCore
namespace Real
namespace P01InputNodeIntegratedMachine

open CanonicalFinalProof
open P01InputReturnMode
open P01InputIndexLookahead
open P01WitnessIndexedReadPreserving
open P01InputAfterReadReturn

/-- One fixed finite-control state space for the complete physical input-node
operation: structural lookahead, preserving indexed witness read, and
mode-aware cursor return. -/
inductive InputNodeState where
  | look : InputIndexLookaheadState → InputNodeState
  | read : InputReturnMode → PreservingReadState → InputNodeState
  | ret : Bool → InputReturnMode → InputAfterReadReturnState → InputNodeState
  | halt : Bool → InputReturnMode → InputNodeState
  | reject
  deriving DecidableEq, Repr

private def liftLookTransition
    (t : InputIndexLookaheadState × Option Bool × Direction) :
    InputNodeState × Option Bool × Direction :=
  match t with
  | (.halt mode, a, d) =>
      (.read mode preservingReadMachine.initial, a, d)
  | (.reject, a, _d) =>
      (.reject, a, .stay)
  | (q, a, d) =>
      (.look q, a, d)

private def liftReadTransition
    (mode : InputReturnMode)
    (t : PreservingReadState × Option Bool × Direction) :
    InputNodeState × Option Bool × Direction :=
  match t with
  | (.halt result, a, d) =>
      (.ret result mode (.start mode), a, d)
  | (.reject, a, _d) =>
      (.reject, a, .stay)
  | (q, a, d) =>
      (.read mode q, a, d)

private def liftReturnTransition
    (result : Bool)
    (t : InputAfterReadReturnState × Option Bool × Direction) :
    InputNodeState × Option Bool × Direction :=
  match t with
  | (.halt mode, a, _d) =>
      (.halt result mode, a, .stay)
  | (.reject, a, _d) =>
      (.reject, a, .stay)
  | (q, a, d) =>
      (.ret result
        (match q with
         | .start mode => mode
         | _ => .done)
        q, a, d)

/-- Single deterministic TM for the physical input-node operation.

The return mode found before the destructive unary-index read is stored in
finite control, so the post-read all-blank region is never reinterpreted
heuristically. -/
def inputNodeMachine : TM InputNodeState (Option Bool) where
  initial := .look inputIndexLookaheadMachine.initial
  blank := none
  transition := fun q a =>
    match q with
    | .look (.halt mode) =>
        (.read mode preservingReadMachine.initial, a, .stay)
    | .look .reject =>
        (.reject, a, .stay)
    | .look q =>
        liftLookTransition
          (inputIndexLookaheadMachine.transition q a)
    | .read mode (.halt result) =>
        (.ret result mode (.start mode), a, .stay)
    | .read _mode .reject =>
        (.reject, a, .stay)
    | .read mode q =>
        liftReadTransition mode
          (preservingReadMachine.transition q a)
    | .ret result mode (.halt _mode') =>
        (.halt result mode, a, .stay)
    | .ret _result _mode .reject =>
        (.reject, a, .stay)
    | .ret result mode q =>
        let t := inputAfterReadReturnMachine.transition q a
        match t with
        | (.halt mode', a', _d) =>
            (.halt result mode', a', .stay)
        | (.reject, a', _d) =>
            (.reject, a', .stay)
        | (q', a', d') =>
            (.ret result mode q', a', d')
    | .halt result mode =>
        (.halt result mode, a, .stay)
    | .reject =>
        (.reject, a, .stay)
  halting := fun q =>
    match q with
    | .halt _ _ => true
    | .reject => true
    | _ => false

@[simp] theorem inputNodeMachine_initial :
    inputNodeMachine.initial =
      .look inputIndexLookaheadMachine.initial := rfl

@[simp] theorem inputNodeMachine_blank :
    inputNodeMachine.blank = none := rfl

@[simp] theorem inputNodeMachine_halt
    (result : Bool) (mode : InputReturnMode) :
    inputNodeMachine.halting (.halt result mode) = true := rfl

@[simp] theorem inputNodeMachine_reject :
    inputNodeMachine.halting .reject = true := rfl

/-- Lookahead terminal states hand the unchanged tape directly to the
preserving reader, retaining the discovered mode in finite control. -/
theorem look_handoff
    (mode : InputReturnMode)
    (tape : Tape (Option Bool)) :
    inputNodeMachine.step
      { state := .look (.halt mode), tape := tape } =
      { state := .read mode preservingReadMachine.initial,
        tape := tape } := by
  rfl

/-- A completed witness read hands the result bit and remembered return mode
to the return phase without changing the tape. -/
theorem read_handoff
    (mode : InputReturnMode) (result : Bool)
    (tape : Tape (Option Bool)) :
    inputNodeMachine.step
      { state := .read mode (.halt result), tape := tape } =
      { state := .ret result mode (.start mode),
        tape := tape } := by
  rfl

/-- A completed return phase becomes the final input-node state while retaining
the witness bit read by the middle phase. -/
theorem return_handoff
    (result : Bool) (mode : InputReturnMode)
    (tape : Tape (Option Bool)) :
    inputNodeMachine.step
      { state := .ret result mode (.halt mode), tape := tape } =
      { state := .halt result mode, tape := tape } := by
  rfl

/-- One active lookahead transition is reproduced exactly by the integrated
machine, except that a newly reached lookahead terminal is immediately encoded
as the corresponding read phase state. -/
theorem look_step_active
    (q : InputIndexLookaheadState)
    (tape : Tape (Option Bool))
    (hhalt :
      inputIndexLookaheadMachine.halting q = false) :
    inputNodeMachine.step
      { state := .look q, tape := tape } =
    let t := inputIndexLookaheadMachine.step
      { state := q, tape := tape }
    match t.state with
    | .halt mode =>
        { state := .read mode preservingReadMachine.initial,
          tape := t.tape }
    | .reject =>
        { state := .reject, tape := t.tape }
    | q' =>
        { state := .look q', tape := t.tape } := by
  cases q <;>
    simp [inputIndexLookaheadMachine] at hhalt
  all_goals
    cases hhead : tape.head with
    | none =>
        simp [inputNodeMachine, liftLookTransition,
          inputIndexLookaheadMachine, TM.step, hhead,
          Tape.write, Tape.move]
    | some b =>
        cases b <;>
          simp [inputNodeMachine, liftLookTransition,
            inputIndexLookaheadMachine, TM.step, hhead,
            Tape.write, Tape.move]

/-- Transition-level preserving-reader simulation.  Keeping this theorem
independent of the tape prevents the large `TM.step` reduction from exploding
across the full preserving-reader state space. -/
theorem read_transition_active
    (mode : InputReturnMode)
    (q : PreservingReadState)
    (symbol : Option Bool)
    (hhalt : preservingReadMachine.halting q = false) :
    inputNodeMachine.transition (.read mode q) symbol =
      liftReadTransition mode (preservingReadMachine.transition q symbol) := by
  cases q <;>
    simp [preservingReadMachine, inputNodeMachine, liftReadTransition] at hhalt ⊢

/-- One active preserving-read step is reproduced exactly, with the mode
threaded through finite control. -/
theorem read_step_active
    (mode : InputReturnMode)
    (q : PreservingReadState)
    (tape : Tape (Option Bool))
    (hhalt : preservingReadMachine.halting q = false) :
    inputNodeMachine.step
      { state := .read mode q, tape := tape } =
    let t := preservingReadMachine.step
      { state := q, tape := tape }
    match t.state with
    | .halt result =>
        { state := .ret result mode (.start mode),
          tape := t.tape }
    | .reject =>
        { state := .reject, tape := t.tape }
    | q' =>
        { state := .read mode q', tape := t.tape } := by
  simp only [TM.step]
  rw [read_transition_active mode q tape.head hhalt]
  generalize ht :
      preservingReadMachine.transition q tape.head = tr
  rcases tr with ⟨q', a', d'⟩
  cases q' <;> rfl

private def liftReturnTransitionStable
    (result : Bool) (mode : InputReturnMode)
    (t : InputAfterReadReturnState × Option Bool × Direction) :
    InputNodeState × Option Bool × Direction :=
  match t with
  | (.halt mode', a, _d) =>
      (.halt result mode', a, .stay)
  | (.reject, a, _d) =>
      (.reject, a, .stay)
  | (q', a, d') =>
      (.ret result mode q', a, d')

/-- Transition-level return simulation with the originally classified mode
retained through every active return state. -/
theorem return_transition_active
    (result : Bool) (mode : InputReturnMode)
    (q : InputAfterReadReturnState)
    (symbol : Option Bool)
    (hhalt : inputAfterReadReturnMachine.halting q = false) :
    inputNodeMachine.transition (.ret result mode q) symbol =
      liftReturnTransitionStable result mode
        (inputAfterReadReturnMachine.transition q symbol) := by
  cases q with
  | start m =>
      cases m <;> cases symbol with
      | none => rfl
      | some b => cases b <;> rfl
  | seekSource =>
      cases symbol with
      | none => rfl
      | some b => cases b <;> rfl
  | scanSource =>
      cases symbol with
      | none => rfl
      | some b => cases b <;> rfl
  | seekFrames =>
      cases symbol with
      | none => rfl
      | some b => cases b <;> rfl
  | scanFrames =>
      cases symbol with
      | none => rfl
      | some b => cases b <;> rfl
  | halt m =>
      simp [inputAfterReadReturnMachine] at hhalt
  | reject =>
      simp [inputAfterReadReturnMachine] at hhalt

/-- One active return step is reproduced exactly, retaining both the read result
and the previously classified return mode. -/
theorem return_step_active
    (result : Bool) (mode : InputReturnMode)
    (q : InputAfterReadReturnState)
    (tape : Tape (Option Bool))
    (hhalt : inputAfterReadReturnMachine.halting q = false) :
    inputNodeMachine.step
      { state := .ret result mode q, tape := tape } =
    let t := inputAfterReadReturnMachine.step
      { state := q, tape := tape }
    match t.state with
    | .halt mode' =>
        { state := .halt result mode', tape := t.tape }
    | .reject =>
        { state := .reject, tape := t.tape }
    | q' =>
        { state := .ret result mode q', tape := t.tape } := by
  simp only [TM.step]
  rw [return_transition_active result mode q tape.head hhalt]
  generalize ht :
      inputAfterReadReturnMachine.transition q tape.head = tr
  rcases tr with ⟨q', a', d'⟩
  cases q' <;> rfl

#print axioms MCore.Real.P01InputNodeIntegratedMachine.look_handoff
#print axioms MCore.Real.P01InputNodeIntegratedMachine.read_handoff
#print axioms MCore.Real.P01InputNodeIntegratedMachine.return_handoff
#print axioms MCore.Real.P01InputNodeIntegratedMachine.look_step_active
#print axioms MCore.Real.P01InputNodeIntegratedMachine.read_step_active
#print axioms MCore.Real.P01InputNodeIntegratedMachine.return_step_active

end P01InputNodeIntegratedMachine
end Real
end MCore
