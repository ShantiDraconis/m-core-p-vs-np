namespace Audit.SAT

abbrev BitStr := List Bool

structure BitEncoding where
  encode : CNF → BitStr
  decode : BitStr → Option CNF
  decode_encode : ∀ φ, decode (encode φ) = some φ

def SATBits (E : BitEncoding) : BitStr → Prop :=
  fun x => ∃ φ : CNF, E.decode x = some φ ∧ Satisfiable φ

def SATEncodingExistence : Prop :=
  Nonempty BitEncoding

/-- Exact remaining realization boundary after the operational F1 model:
an actual encoding plus a polynomial-time NTM deciding its SAT language. -/
def SATOfficialNPRealization (E : BitEncoding) : Prop :=
  Audit.OfficialModel.OfficialNP (SATBits E)

def SATNPBridge : Prop :=
  ∃ E : BitEncoding, SATOfficialNPRealization E

structure ManyOneReduction
    (A B : BitStr → Prop) where
  map : BitStr → BitStr
  correct : ∀ x, A x ↔ B (map x)

/-- Semantic part of Cook-Levin after an encoding is fixed.  Polynomial-time
computability of the map is deliberately not hidden in this structure. -/
def CookLevinSemanticBoundary (E : BitEncoding) : Prop :=
  ∀ L : Audit.OfficialModel.OfficialLanguage,
    Audit.OfficialModel.OfficialNP L →
    Nonempty (ManyOneReduction L (SATBits E))

/-- The missing complexity requirement is explicit: the reduction map above
still needs a genuine polynomial-time transducer realization. -/
def CookLevinPolytimeMapStatus : String :=
  "OPEN_FORMALIZATION_POLYTIME_TRANSDUCER"

def CookLevinBridgeStatus : String :=
  "SEMANTIC_REDUCTION_TYPED / POLYTIME_MAP_OPEN"

end Audit.SAT
