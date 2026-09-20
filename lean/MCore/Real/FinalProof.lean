import MCore.Real.SATMachine

namespace MCore
namespace Real

open CircuitK1

/-- Languages over the repository's concrete Circuit input type. -/
abbrev CircuitLanguage := Circuit → Prop

/-- Explicit polynomial bound for the concrete machine model.
    The coefficient and exponent are fixed for the machine, not for the input. -/
def PolynomialTimeBound (T : TimeBound) : Prop :=
  ∃ coefficient exponent : Nat, ∀ n : Nat,
    T n ≤ coefficient * (n + 1) ^ exponent

/-- Deterministic polynomial-time realization of one Circuit language.
    Acceptance is read from the halting state; the input-dependent encoder is
    forbidden from changing the machine control state. -/
structure PolyDTMRealization (language : CircuitLanguage) where
  State : Type
  Symbol : Type
  machine : TM State Symbol
  accepting : State → Bool
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  time_poly :
    PolynomialTimeBound timeBound
  decides :
    ∀ φ : Circuit,
      machine.HaltsWithin (timeBound (CircuitK1.size φ)) (encode φ) ∧
      (accepting
          (machine.run (timeBound (CircuitK1.size φ)) (encode φ)).state = true
        ↔ language φ)

/-- Nondeterministic polynomial-time realization of one Circuit language.
    This reuses the already-certified NTM.DecidesWithin contract. -/
structure PolyNTMRealization (language : CircuitLanguage) where
  State : Type
  Symbol : Type
  machine : NTM State Symbol
  encode : Circuit → Configuration State Symbol
  timeBound : TimeBound
  encode_initial :
    ∀ φ : Circuit, (encode φ).state = machine.initial
  time_poly :
    PolynomialTimeBound timeBound
  decides :
    NTM.DecidesWithin
      machine encode CircuitK1.size language timeBound

/-- Concrete machine-model P and NP predicates used by the direct final-proof
    attack. These are internal definitions; equivalence with any external
    presentation of P/NP is a separate model-equivalence theorem. -/
def InP (language : CircuitLanguage) : Prop :=
  Nonempty (PolyDTMRealization language)

def InNP (language : CircuitLanguage) : Prop :=
  Nonempty (PolyNTMRealization language)

/-- Separation endpoint for the concrete machine model. -/
def MachinePneqNP : Prop :=
  ¬ ∀ language : CircuitLanguage, InP language ↔ InNP language

/-- SAT is in NP for this model. Constructing this witness is infrastructure,
    not the separation lower bound itself. -/
def SATInNP : Prop :=
  InNP SATLanguage

/-- Direct lower-bound target: no deterministic polynomial-time realization
    decides SAT in this concrete model. -/
def SATNotInP : Prop :=
  ¬ InP SATLanguage

/-- Positive certificate form of the lower-bound target.
    This is the fail-closed analogue of a positive numerical certificate:
    every proposed deterministic polynomial-time SAT decider is excluded. -/
structure SATLowerBoundCertificate : Prop where
  excludes :
    ∀ candidate : PolyDTMRealization SATLanguage, False

theorem sat_not_in_p_of_lower_bound_certificate
    (cert : SATLowerBoundCertificate) :
    SATNotInP := by
  intro hP
  rcases hP with ⟨candidate⟩
  exact cert.excludes candidate

theorem lower_bound_certificate_of_sat_not_in_p
    (hNotP : SATNotInP) :
    SATLowerBoundCertificate := by
  refine ⟨?_⟩
  intro candidate
  exact hNotP ⟨candidate⟩

theorem sat_lower_bound_certificate_iff :
    SATLowerBoundCertificate ↔ SATNotInP := by
  constructor
  · exact sat_not_in_p_of_lower_bound_certificate
  · exact lower_bound_certificate_of_sat_not_in_p

/-- Direct endpoint compression. No NP-completeness theorem is required:
    one language in NP but outside P already separates the two classes. -/
theorem sat_boundary_implies_machine_p_ne_np
    (hNP : SATInNP)
    (hNotP : SATNotInP) :
    MachinePneqNP := by
  intro hEq
  exact hNotP ((hEq SATLanguage).mpr hNP)

/-- Certificate-shaped final theorem. -/
theorem sat_certificate_implies_machine_p_ne_np
    (hNP : SATInNP)
    (cert : SATLowerBoundCertificate) :
    MachinePneqNP :=
  sat_boundary_implies_machine_p_ne_np
    hNP (sat_not_in_p_of_lower_bound_certificate cert)

/-- The direct FINAL_PROOF residual.
    The first conjunct is the concrete NP witness.
    The second conjunct is the genuine universal deterministic lower bound.
    No benchmark, finite search, C12/C13 table, or elliptic-curve timing result
    inhabits this proposition by definition. -/
def FINAL_PROOF_RESIDUAL : Prop :=
  SATInNP ∧ SATLowerBoundCertificate

theorem final_proof_from_residual
    (h : FINAL_PROOF_RESIDUAL) :
    MachinePneqNP := by
  exact sat_certificate_implies_machine_p_ne_np h.1 h.2

#print axioms MCore.Real.sat_not_in_p_of_lower_bound_certificate
#print axioms MCore.Real.sat_boundary_implies_machine_p_ne_np
#print axioms MCore.Real.sat_certificate_implies_machine_p_ne_np
#print axioms MCore.Real.final_proof_from_residual

end Real
end MCore
