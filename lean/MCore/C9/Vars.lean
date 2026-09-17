import MCore.C9.Reuse

namespace MCore
namespace C9

/-- All input-variable identifiers occurring syntactically in a formula tree. -/
def freeVarList : FormulaTree → List Nat
  | .input i => [i]
  | .const _ => []
  | .not c => freeVarList c
  | .and a b => freeVarList a ++ freeVarList b
  | .or a b => freeVarList a ++ freeVarList b

/-- Number of distinct syntactically free input variables.
This deliberately does not attempt semantic relevance minimization. -/
def vars (t : FormulaTree) : Nat :=
  (freeVarList t).eraseDups.length

@[simp] theorem vars_const (b : Bool) : vars (.const b) = 0 := by
  unfold vars freeVarList
  decide

@[simp] theorem vars_input (i : Nat) : vars (.input i) = 1 := by
  unfold vars freeVarList
  simp only [List.eraseDups_cons, List.mem_nil, Bool.false_eq_true, ↓reduceIte, List.length_cons,
    List.length_nil]

end C9
end MCore
