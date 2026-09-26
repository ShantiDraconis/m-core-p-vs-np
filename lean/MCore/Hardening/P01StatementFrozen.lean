import MCore.Real.P01FinalCertificate
import MCore.Hardening.Base

namespace MCore.Hardening.P01StatementFrozen

open MCore.Real.P01FinalCertificate

/-- Exact frozen P01 statement. No weakening, wrapper hypothesis, or endpoint
substitution is permitted under this hash. -/
abbrev Statement : Prop := Nonempty P01MachineConstruction

def canonicalText : String :=
  "Nonempty MCore.Real.P01FinalCertificate.P01MachineConstruction"

def statementHash : String :=
  "sha256:da4ad11e047a06464bdfb4add0697fa5dd98e3c7e0432d75d821c4fafbe98b20"

def policy := MCore.Hardening.p01Policy

end MCore.Hardening.P01StatementFrozen
