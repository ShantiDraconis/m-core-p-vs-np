import MCore.C12.Families

namespace MCore
namespace Real

open CircuitK1
open C12

/-- A propositional literal in the existing Circuit AST. -/
def IsLiteral : Circuit → Prop
  | .input _ => True
  | .not (.input _) => True
  | _ => False

/-- A clause is a literal, an OR-tree of clauses, or the empty clause `false`. -/
def IsClause : Circuit → Prop
  | .const false => True
  | .input _ => True
  | .not (.input _) => True
  | .or a b => IsClause a ∧ IsClause b
  | _ => False

/-- CNF is a clause, an AND-tree of CNFs, or an empty conjunction/empty clause. -/
def IsCNF : Circuit → Prop
  | .const true => True
  | .const false => True
  | .input _ => True
  | .not (.input _) => True
  | .or a b => IsClause (.or a b)
  | .and a b => IsCNF a ∧ IsCNF b
  | _ => False

@[simp] theorem isLiteral_input (i : Nat) :
    IsLiteral (.input i) := trivial

@[simp] theorem isLiteral_not_input (i : Nat) :
    IsLiteral (.not (.input i)) := trivial

@[simp] theorem emptyClause_isClause :
    IsClause (.const false) := trivial

@[simp] theorem emptyCNF_isCNF :
    IsCNF (.const true) := trivial

@[simp] theorem emptyClause_isCNF :
    IsCNF (.const false) := trivial

/-- Structural closure of clauses under disjunction. -/
theorem IsClause_or {a b : Circuit} (ha : IsClause a) (hb : IsClause b) :
    IsClause (.or a b) :=
  ⟨ha, hb⟩

/-- Structural closure of CNFs under conjunction. -/
theorem IsCNF_and {a b : Circuit} (ha : IsCNF a) (hb : IsCNF b) :
    IsCNF (.and a b) :=
  ⟨ha, hb⟩

/-- Every literal produced by C12.literalAt has literal shape. -/
theorem literalAt_isLiteral
    (nVars seed clauseIdx pos : Nat) :
    IsLiteral (C12.literalAt nVars seed clauseIdx pos) := by
  unfold C12.literalAt
  exact dite
    ((seed + clauseIdx + pos) % 2 = 0)
    (fun _ => True.intro)
    (fun _ => True.intro)

end Real
end MCore
