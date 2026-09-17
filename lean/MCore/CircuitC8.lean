import MCore.CircuitC7

namespace MCore
namespace CircuitC8

open CircuitK1 CircuitC2 CircuitC3 CircuitC4 CircuitC5 CircuitC6 CircuitC7

structure RecurrenceBranch where
  fixedVars : Nat
  potentialDrop : Nat

def BranchProgress (b : RecurrenceBranch) : Prop :=
  0 < b.fixedVars ∨ 0 < b.potentialDrop

/-- Scalar rank for finite restriction descent. -/
def recurrenceRank (vars potential : Nat) : Nat :=
  vars * (potential + 1) + potential

/-- Fixing at least one available variable strictly lowers the rank when the
potential does not increase. The proof keeps multiplication monotonicity
explicit and leaves only linear inequalities to `omega`. -/
theorem rank_decreases_when_variable_fixed
    (vars potential fixedVars newPotential : Nat)
    (hfix : 0 < fixedVars) (hfixle : fixedVars ≤ vars)
    (hpot : newPotential ≤ potential) :
    recurrenceRank (vars - fixedVars) newPotential < recurrenceRank vars potential := by
  unfold recurrenceRank
  have hv : vars - fixedVars < vars := by omega
  have hmul : (vars - fixedVars) * (potential + 1) < vars * (potential + 1) :=
    Nat.mul_lt_mul_of_pos_right hv (Nat.succ_pos potential)
  have hleft : (vars - fixedVars) * (newPotential + 1) ≤
      (vars - fixedVars) * (potential + 1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hpot)
  have hsum : (vars - fixedVars) * (newPotential + 1) + newPotential ≤
      (vars - fixedVars) * (potential + 1) + potential :=
    Nat.add_le_add hleft hpot
  have hstrict : (vars - fixedVars) * (potential + 1) + potential <
      vars * (potential + 1) + potential :=
    Nat.add_lt_add_right hmul potential
  exact Nat.lt_of_le_of_lt hsum hstrict

/-- At fixed variable count, strict potential decrease strictly lowers rank. -/
theorem rank_decreases_when_potential_drops
    (vars potential newPotential : Nat)
    (hpot : newPotential < potential) :
    recurrenceRank vars newPotential < recurrenceRank vars potential := by
  unfold recurrenceRank
  have hs : newPotential + 1 ≤ potential + 1 := Nat.succ_le_succ (Nat.le_of_lt hpot)
  have hm : vars * (newPotential + 1) ≤ vars * (potential + 1) :=
    Nat.mul_le_mul_left vars hs
  have hsum : vars * (newPotential + 1) + newPotential <
      vars * (potential + 1) + potential :=
    Nat.add_lt_add_of_le_of_lt hm hpot
  exact hsum

theorem good_mass_supplies_aggregate_progress
    (sample : List WeightedRestriction) (c : Circuit)
    (minGoodWeight minDrop : Nat)
    (h : GoodMassWitness sample c minGoodWeight minDrop) :
    minDrop * minGoodWeight ≤ weightedDrop sample c :=
  good_mass_implies_weightedDrop_lower_bound sample c minGoodWeight minDrop h

/-- Positive runtime saving is intentionally a separate obligation. -/
def RuntimeSavingWitness (saving : Nat) : Prop := 0 < saving

theorem zero_is_not_runtime_saving : ¬ RuntimeSavingWitness 0 := by
  simp [RuntimeSavingWitness]

theorem c8_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c7_classical_endpoint_not_promoted

theorem c8_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c7_k10_not_promoted

end CircuitC8
end MCore
