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

/-- A single canonical CNF has a uniform local branching deficit of at least c. -/
def DeficitAtLeast (c : Nat) (f : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ (cnfCircuit f) →
      amortizedDrop 1 1 ρ (cnfCircuit f) ≤
        costBits ρ (cnfCircuit f) ∧
      c ≤ costBits ρ (cnfCircuit f) -
        amortizedDrop 1 1 ρ (cnfCircuit f)

/-- Hard canonical-CNF subfamily.  The hardness predicate is not a new syntax:
it is a semantic/quantitative filter on the repository's existing CNF type. -/
def HardCNFSubfamilyWithMargin
    (c : Nat)
    (clauseBound : Nat → Nat)
    (n : Nat) (f : CNF) : Prop :=
  GeneralCNFFamily clauseBound n f ∧ DeficitAtLeast c f

theorem hardCNF_excludes_payoff
    {c : Nat} {f : CNF}
    (hc : 0 < c)
    (h : DeficitAtLeast c f) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ (cnfCircuit f) →
        ¬ PaysOff 1 1 ρ (cnfCircuit f) := by
  intro ρ hprog hpay
  have hdef := (h ρ hprog).1
  have hlt :=
    paysOff_implies_costBits_lt_amortizedDrop
      1 1 ρ (cnfCircuit f) hpay
  omega

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

theorem hardSubfamily_has_uniform_deficit
    {c : Nat} (hc : 0 < c)
    (clauseBound : Nat → Nat) :
    UniformPersistentDeficit
      (HardCNFSubfamilyWithMargin c clauseBound) := by
  refine ⟨c, 0, hc, ?_⟩
  intro n hn f hf ρ hprog
  exact hf.2 ρ hprog

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

/-- A restriction is core-dominated when it gives progress on the padded
formula and independently gives progress on the hard core.  This excludes the
vacuous empty-core counterexample and records the exact guard needed by the
inheritance theorem. -/
def CoreDominatedProgress
    (ρ : Restriction)
    (f core : CNF) : Prop :=
  RestrictionProgress ρ (cnfCircuit (f ++ core)) ∧
  RestrictionProgress ρ (cnfCircuit core)

/-- Guarded deficit inheritance.  Unlike raw append inheritance, this only
claims inheritance for restrictions whose progress is witnessed on the core. -/
def CoreDominatedDeficitInheritance
    (core : Nat → CNF)
    (c : Nat) : Prop :=
  ∀ (n : Nat) (f : CNF) (ρ : Restriction),
    DeficitAtLeast c (core n) →
    CoreDominatedProgress ρ f (core n) →
      amortizedDrop 1 1 ρ (cnfCircuit (f ++ core n)) ≤
        costBits ρ (cnfCircuit (f ++ core n)) ∧
      c ≤ costBits ρ (cnfCircuit (f ++ core n)) -
        amortizedDrop 1 1 ρ (cnfCircuit (f ++ core n))

/-- A usable hard-core family for the guarded padding route. -/
structure HardCoreFamily where
  core : Nat → CNF
  margin : Nat
  margin_pos : 0 < margin
  satisfiable :
    ∀ n, CircuitK1.SATLanguage (cnfCircuit (core n))
  deficit :
    ∀ n, DeficitAtLeast margin (core n)
  dominated_inherits :
    CoreDominatedDeficitInheritance core margin

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

/-- Exact dominance obligation needed by the guarded route: every restriction
that makes progress on the padded output must also make progress on the core. -/
def CoreProgressDominates
    (payload core : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ (cnfCircuit (payload ++ core)) →
      RestrictionProgress ρ (cnfCircuit core)

theorem coreProgressDominates_to_coreDominated
    {payload core : CNF}
    (h : CoreProgressDominates payload core) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ (cnfCircuit (payload ++ core)) →
        CoreDominatedProgress ρ payload core := by
  intro ρ hprog
  exact ⟨hprog, h ρ hprog⟩

/-- Reduction specialized to the hard-core construction.  Besides semantic
correctness, it must expose that every progressing restriction relevant to the
lower-bound argument is core-dominated. -/
structure SATReductionIntoCoreDominatedFamily
    (H : HardCoreFamily)
    (Family : Nat → CNF → Prop) extends SATReductionIntoFamily Family where
  payload : BitString → CNF
  reduce_eq :
    ∀ x, reduce x = payload x ++ H.core (parameter x)
  progress_dominance :
    ∀ x,
      CoreProgressDominates (payload x) (H.core (parameter x))
  every_progress_core_dominated :
    ∀ x ρ,
      RestrictionProgress ρ (cnfCircuit (reduce x)) →
      CoreDominatedProgress ρ (payload x) (H.core (parameter x)) := by
    intro x ρ hprog
    rw [reduce_eq x] at hprog
    exact coreProgressDominates_to_coreDominated
      (progress_dominance x) ρ hprog

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
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.hardCNF_excludes_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.hardSubfamily_has_uniform_deficit
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.uniformPersistentDeficit_excludes_eventual_payoff
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.coreProgressDominates_to_coreDominated
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.transfer_closes_p02

end P02RestrictionLowerBoundPattern
end Real
end MCore
