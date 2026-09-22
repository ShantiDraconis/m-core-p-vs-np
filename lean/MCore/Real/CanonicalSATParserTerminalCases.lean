import MCore.Real.CanonicalSATParserLeafSourceProof
import MCore.Real.CanonicalSATParserReturnProof

namespace MCore
namespace Real
namespace CanonicalSATParserTerminalCases

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserLeafReturnProof
open CanonicalSATParserLeafSourceProof
open CanonicalSATParserReturnProof

/-- If a leaf consumed the last active slot while unread source still remains,
state 16 rejects in exactly one step. -/
theorem leaf16_nonempty_rejects
    (pad : Nat)
    (last : Bool)
    (rest : BitString)
    (right : List (Option Bool)) :
    parserMachine.step
        (leafSourceCheckConfig 16
          (some last :: (rest.map some ++
            List.replicate pad (none : Option Bool)))
          right) =
      { state := (24 : Fin 25)
        tape :=
          Tape.move none .left
            { left :=
                rest.map some ++
                  List.replicate pad (none : Option Bool)
              head := some last
              right := none :: right } } := by
  cases rest <;>
    simp [leafSourceCheckConfig, parserMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- State 21 rejects when a binary constructor has opened a new slot but the
source is already exhausted.  This is the exact malformed-prefix terminal
case needed by the global parser induction. -/
theorem binary_check_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (right : List (Option Bool)) :
    parserMachine.run 2
        (binaryReturnConfig []
          (List.replicate pad (none : Option Bool))
          right) =
      { state := (24 : Fin 25)
        tape :=
          Tape.move none .left
            { left := List.replicate pad (none : Option Bool)
              head := none
              right := none :: right } } := by
  cases pad with
  | zero => omega
  | succ p =>
      simp [binaryReturnConfig, parserMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ]

#print axioms MCore.Real.CanonicalSATParserTerminalCases.leaf16_nonempty_rejects
#print axioms MCore.Real.CanonicalSATParserTerminalCases.binary_check_exhausted_rejects

end CanonicalSATParserTerminalCases
end Real
end MCore
