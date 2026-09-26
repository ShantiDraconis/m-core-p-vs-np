import MCore.Real.P01PhysicalDispatcher

namespace MCore
namespace Real
namespace P01PhysicalDispatcherBridge

open P01PhysicalDispatcher
open P01FullVerifierPhysicalControl
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

theorem control_transition_lift
    (q : Fin 8) (s : Option Bool) :
    physicalDispatcherMachine.transition (controlState q) s =
      let t := decoderEvaluatorMachine.transition q s
      (controlState t.1, t.2.1, t.2.2) := by
  simp [physicalDispatcherMachine, controlState, asControl, liftControl]

theorem stack_transition_lift
    (q : Fin 8) (s : Option Bool) :
    physicalDispatcherMachine.transition (stackState q) s =
      let t := stackPrimitiveMachine.transition q s
      (stackState t.1, t.2.1, t.2.2) := by
  simp [physicalDispatcherMachine, stackState, asStack, liftStack]
  omega

theorem witness_transition_lift
    (q : Fin 6) (s : Option Bool) :
    physicalDispatcherMachine.transition (witnessReadState q) s =
      let t := witnessIndexedReadMachine.transition q s
      (witnessReadState t.1, t.2.1, t.2.2) := by
  simp [physicalDispatcherMachine, witnessReadState, asWitness, liftWitness]
  omega

theorem rewind_transition_lift
    (q : Fin 3) (s : Option Bool) :
    physicalDispatcherMachine.transition (rewindState q) s =
      let t := sourceRewindMachine.transition q s
      (rewindState t.1, t.2.1, t.2.2) := by
  simp [physicalDispatcherMachine, rewindState, asRewind, liftRewind]
  omega

theorem dispatcher_accept_halts :
    physicalDispatcherMachine.halting acceptState = true := by
  simp [physicalDispatcherMachine, acceptState]

theorem dispatcher_reject_halts :
    physicalDispatcherMachine.halting rejectState = true := by
  simp [physicalDispatcherMachine, rejectState]

#print axioms MCore.Real.P01PhysicalDispatcherBridge.control_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.stack_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.witness_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.rewind_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.dispatcher_accept_halts
#print axioms MCore.Real.P01PhysicalDispatcherBridge.dispatcher_reject_halts

end P01PhysicalDispatcherBridge
end Real
end MCore
