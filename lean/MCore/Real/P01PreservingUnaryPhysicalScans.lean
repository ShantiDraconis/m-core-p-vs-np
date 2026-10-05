import MCore.Real.P01PreservingUnaryWitnessMachine

namespace MCore
namespace Real
namespace P01PreservingUnaryPhysicalScans

open P01PreservingUnaryWitnessMachine

/-- Physical scan across a block of erased unary markers.
Starting on a blank with k further blanks to the left, k+1 steps expose
the first Boolean cell and preserve all symbols. -/
theorem seekBlanks_run_replicate
    (k : Nat) (leftBits : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 1)
      { state := .seekBlanks
        tape :=
          { left := List.replicate k none ++ some bit :: leftBits
            head := none
            right := right } } =
      { state := .seekBlanks
        tape :=
          { left := leftBits
            head := some bit
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      simpa [Nat.succ_eq_add_one, List.replicate_succ,
        preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.append_assoc] using
        ih (right := none :: right)

#print axioms MCore.Real.P01PreservingUnaryPhysicalScans.seekBlanks_run_replicate

end P01PreservingUnaryPhysicalScans
end Real
end MCore
