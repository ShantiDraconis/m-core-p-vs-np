import MCore.C11.BranchingCost
import MCore.Real.P02BoundedComputationEncoding
import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P02RestrictionLowerBoundPattern

open C9 C10 C11 CircuitK1
open P02BoundedComputationEncoding

/-- Exact amortized structural drop used by C11, evaluated on the canonical
Circuit view of a CNF. -/
def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

theorem paysOff_implies_costBits_lt_amortizedDrop
    (α β : Nat) (ρ : Restriction) (t : FormulaTree)
    (h : PaysOff α β ρ t) :
    costBits ρ t < amortizedDrop α β ρ t := by
  unfold PaysOff amortizedDrop at *
  omega

def PersistentBranchingDeficit
    (α β : Nat) (t : FormulaTree) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ t →
      amortizedDrop α β ρ t ≤ costBits ρ t

theorem persistentBranchingDeficit_excludes_payoff
    (α β : Nat) (t : FormulaTree)
    (h : PersistentBranchingDeficit α β t) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ t →
        ¬ PaysOff α β ρ t := by
  intro ρ hprog hpay
  have hlt := paysOff_implies_costBits_lt_amortizedDrop α β ρ t hpay
  have hle := h ρ hprog
  omega

/-- Canonical CNF variable bound: one plus the largest variable identifier. -/
def clauseVarBound (c : Clause) : Nat :=
  c.foldl (fun acc l => max acc (l.var + 1)) 0

def cnfVarBound (f : CNF) : Nat :=
  f.foldl (fun acc c => max acc (clauseVarBound c)) 0

/-- General bounded CNF family over the repository's canonical CNF type.
This is useful as an ambient family, but is not claimed to satisfy a persistent
deficit universally. -/
def GeneralCNFFamily
    (clauseBound : Nat → Nat) (n : Nat) (f : CNF) : Prop :=
  cnfVarBound f ≤ n ∧ f.length ≤ clauseBound n

/-- A hard subfamily is a predicate on the canonical CNF type, refined by the
same explicit size envelope used by the reduction. -/
def HardCNFSubfamily
    (IsHardCNF : CNF → Prop)
    (clauseBound : Nat → Nat)
    (n : Nat) (f : CNF) : Prop :=
  IsHardCNF f ∧ GeneralCNFFamily clauseBound n f

/-- Uniform positive deficit on every progressing restriction of every member
of a parametrized canonical-CNF family. -/
def UniformPersistentDeficit
    (Family : Nat → CNF → Prop) : Prop :=
  ∃ (c n0 : Nat), 0 < c ∧
    ∀ n : Nat, n0 ≤ n →
      ∀ f : CNF, Family n f →
        ∀ ρ : Restriction,
          RestrictionProgress ρ (cnfCircuit f) →
            amortizedDrop 1 1 ρ (cnfCircuit f) ≤
              costBits ρ (cnfCircuit f) ∧
            c ≤ costBits ρ (cnfCircuit f) -
              amortizedDrop 1 1 ρ (cnfCircuit f)

abbrev PersistentBranchingDeficitFamily :=
  UniformPersistentDeficit

theorem uniformPersistentDeficit_excludes_eventual_payoff
    {Family : Nat → CNF → Prop}
    (h : UniformPersistentDeficit Family) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ∀ f : CNF, Family n f →
        ∀ ρ : Restriction,
          RestrictionProgress ρ (cnfCircuit f) →
            ¬ PaysOff 1 1 ρ (cnfCircuit f) := by
  rcases h with ⟨c, n0, hc, h⟩
  refine ⟨n0, ?_⟩
  intro n hn f hf ρ hprog hpay
  have hdef := (h n hn f hf ρ hprog).1
  have hlt :=
    paysOff_implies_costBits_lt_amortizedDrop
      1 1 ρ (cnfCircuit f) hpay
  omega

/-- Polynomial SAT reduction into a parametrized family of canonical CNFs. -/
structure SATReductionIntoFamily
    (Family : Nat → CNF → Prop) where
  reduce : BitString → CNF
  parameter : BitString → Nat
  parameterBound : Nat → Nat
  parameter_poly : CanonicalFinalProof.PolynomialTimeBound parameterBound
  parameter_le : ∀ x, parameter x ≤ parameterBound x.length
  lands : ∀ x, Family (parameter x) (reduce x)
  correct :
    ∀ x,
      CanonicalSATBoundary.SATBits
          CanonicalCircuitBits.circuitBitEncoding x ↔
        CircuitK1.SATLanguage (cnfCircuit (reduce x))

/-- Explicit simulation obligation: a polynomial DTM for canonical SAT must
induce a restriction-tree procedure on the hard family. The theorem carrying
the exponential lower bound belongs here; it is not inferred from C11 alone. -/
structure DTMToRestrictionTreeAdapter
    (Family : Nat → CNF → Prop) where
  deficit_excludes_poly_sat :
    Nonempty (SATReductionIntoFamily Family) →
    UniformPersistentDeficit Family →
    ¬ CanonicalFinalProof.InP
      (CanonicalSATBoundary.SATBits
        CanonicalCircuitBits.circuitBitEncoding)

def RestrictionLowerBoundTransfer
    (Family : Nat → CNF → Prop) : Prop :=
  Nonempty (SATReductionIntoFamily Family) ∧
  Nonempty (DTMToRestrictionTreeAdapter Family) ∧
  UniformPersistentDeficit Family

theorem transfer_closes_p02
    {Family : Nat → CNF → Prop}
    (h : RestrictionLowerBoundTransfer Family) :
    P02TerminalFrontier.P02Target := by
  rcases h with ⟨hRed, hAdapter, hDeficit⟩
  rcases hAdapter with ⟨A⟩
  exact P02TerminalFrontier.p02_target_iff_sat_not_in_p.mpr
    (A.deficit_excludes_poly_sat hRed hDeficit)

#print axioms MCore.Real.P02RestrictionLowerBoundPattern.paysOff_implies_costBits_lt_amortizedDrop
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.persistentBranchingDeficit_excludes_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.uniformPersistentDeficit_excludes_eventual_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.transfer_closes_p02

end P02RestrictionLowerBoundPattern
end Real
end MCore
