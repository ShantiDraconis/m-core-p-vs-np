import MCore.Real.P01TerminalMaterialCertificate

namespace MCore.Real.P01MachineConstructionAttempt

/-- The historical machine-construction obligation, discharged by the checked decoder. -/
def myP01Construction : P01FinalCertificate.P01ConstructionGap :=
  P01TerminalMaterialCertificate.p01_closed_no_hypothesis

#print axioms myP01Construction

end MCore.Real.P01MachineConstructionAttempt
