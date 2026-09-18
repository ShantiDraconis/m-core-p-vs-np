import MCore.C11.BranchingCost

namespace MCore
namespace C12

open C9 C10 C11 CircuitK1 CircuitC2

def orFrom (start : Nat) : Nat → FormulaTree
  | 0 => .const false
  | n + 1 => .or (.input (start + n)) (orFrom start n)

def andFrom (start : Nat) : Nat → FormulaTree
  | 0 => .const true
  | n + 1 => .and (.input (start + n)) (andFrom start n)

def orN (n : Nat) : FormulaTree := orFrom 0 n

def andN (n : Nat) : FormulaTree := andFrom 0 n

/-- A family whose first input becomes a simplifiable neutral factor when fixed true. -/
def reducibleN (n : Nat) : FormulaTree :=
  .and (.input 0) (orFrom 1 n)

def fixPrefix (k : Nat) (b : Bool) : Restriction := fun i =>
  if i < k then some b else none

def fixPrefixAlternating (k : Nat) : Restriction := fun i =>
  if i < k then
    if i % 2 = 0 then some true else some false
  else none

def pseudoVar (nVars seed clauseIdx pos : Nat) : Nat :=
  let m := if nVars = 0 then 1 else nVars
  (seed * 97 + clauseIdx * 31 + pos * 17 + clauseIdx * pos * 7 + 11) % m

def literalAt (nVars seed clauseIdx pos : Nat) : FormulaTree :=
  let v := pseudoVar nVars seed clauseIdx pos
  if (seed + clauseIdx + pos) % 2 = 0 then
    .input v
  else
    .not (.input v)

def randomClause (nVars seed clauseIdx : Nat) : Nat → FormulaTree
  | 0 => .const false
  | width + 1 =>
      .or (literalAt nVars seed clauseIdx width)
        (randomClause nVars seed clauseIdx width)

def randomKCNF (nVars clauses width seed : Nat) : FormulaTree :=
  match clauses with
  | 0 => .const true
  | c + 1 =>
      .and (randomClause nVars seed c width)
        (randomKCNF nVars c width seed)

inductive Family where
  | orN
  | andN
  | reducibleN
  | randomKCNF
  deriving DecidableEq, Repr

def familyName : Family → String
  | .orN => "or_n"
  | .andN => "and_n"
  | .reducibleN => "reducible_n"
  | .randomKCNF => "random_k_cnf"

/-- C12 records a family-level quantitative question without promoting it to a theorem. -/
def FamilyPayoffObligation (α β : Nat) (f : Nat → FormulaTree) : Prop :=
  ∀ n, 0 < n → ∃ ρ : Restriction, PaysOff α β ρ (f n)

theorem c12_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c11_classical_endpoint_not_promoted

theorem c12_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c11_k10_not_promoted

end C12
end MCore
