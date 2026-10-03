import MCore.Real.SevenLaneGreenGate

namespace MCore.Real.SevenLaneClaimBoundary

inductive ClaimKind where
  | skeleton
  | sourceMiddleOnly
  | realFrontierBound
  | historicallySolvedExternal
  deriving Repr, DecidableEq, BEq

structure LaneClaim where
  lane : String
  closedBaseCount : Nat
  closedBridgeCount : Nat
  sourceMiddleCount : Nat
  materialGaps : Nat
  materialAtoms : Nat
  claimKind : ClaimKind
  terminalEndpointClosed : Bool
  buildVerified : Bool
  green : Bool
  deriving Repr, DecidableEq

def p01 : LaneClaim :=
  { lane := "P01_Riemann"
    closedBaseCount := 3
    closedBridgeCount := 0
    sourceMiddleCount := 1
    materialGaps := 1
    materialAtoms := 1
    claimKind := .sourceMiddleOnly
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p02 : LaneClaim :=
  { lane := "P02_YangMills"
    closedBaseCount := 4
    closedBridgeCount := 1
    sourceMiddleCount := 0
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p03 : LaneClaim :=
  { lane := "P03_PvsNP"
    closedBaseCount := 6
    closedBridgeCount := 4
    sourceMiddleCount := 2
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p04 : LaneClaim :=
  { lane := "P04_NavierStokes"
    closedBaseCount := 4
    closedBridgeCount := 2
    sourceMiddleCount := 0
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p05 : LaneClaim :=
  { lane := "P05_Hodge"
    closedBaseCount := 4
    closedBridgeCount := 2
    sourceMiddleCount := 0
    materialGaps := 1
    materialAtoms := 1
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p06 : LaneClaim :=
  { lane := "P06_BSD"
    closedBaseCount := 4
    closedBridgeCount := 2
    sourceMiddleCount := 0
    materialGaps := 1
    materialAtoms := 2
    claimKind := .realFrontierBound
    terminalEndpointClosed := false
    buildVerified := false
    green := false }

def p07 : LaneClaim :=
  { lane := "P07_Poincare"
    closedBaseCount := 0
    closedBridgeCount := 0
    sourceMiddleCount := 0
    materialGaps := 0
    materialAtoms := 0
    claimKind := .historicallySolvedExternal
    terminalEndpointClosed := true
    buildVerified := false
    green := false }

/-- The six currently open Millennium lanes tracked by this repository. -/
def openLaneClaims : List LaneClaim := [p01, p02, p03, p04, p05, p06]

def realFrontierBoundCount : Nat :=
  openLaneClaims.foldl
    (fun n L => if L.claimKind == .realFrontierBound then n + 1 else n) 0

def locallyGreenOpenLaneCount : Nat :=
  openLaneClaims.foldl (fun n L => if L.green then n + 1 else n) 0

theorem five_open_lanes_have_real_frontier_bound :
    realFrontierBoundCount = 5 := by decide

theorem no_open_lane_claims_terminal_closure :
    openLaneClaims.all (fun L => !L.terminalEndpointClosed) = true := by
  decide

theorem no_open_lane_claims_local_green :
    locallyGreenOpenLaneCount = 0 := by
  decide

/--
A frontier claim is strictly weaker than a solution claim in the current
manifest: every open lane has terminalEndpointClosed=false.
-/
theorem frontier_claim_not_solution_claim :
    ∀ L ∈ openLaneClaims, L.terminalEndpointClosed = false := by
  intro L hL
  simp [openLaneClaims] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/--
P07 is recorded as historically solved externally; this does not manufacture a
local build-verified formal proof in the current repository.
-/
theorem poincare_external_not_local_build :
    p07.claimKind = .historicallySolvedExternal ∧
    p07.terminalEndpointClosed = true ∧
    p07.buildVerified = false := by
  decide

#print axioms MCore.Real.SevenLaneClaimBoundary.five_open_lanes_have_real_frontier_bound
#print axioms MCore.Real.SevenLaneClaimBoundary.no_open_lane_claims_terminal_closure
#print axioms MCore.Real.SevenLaneClaimBoundary.no_open_lane_claims_local_green
#print axioms MCore.Real.SevenLaneClaimBoundary.frontier_claim_not_solution_claim
#print axioms MCore.Real.SevenLaneClaimBoundary.poincare_external_not_local_build

end MCore.Real.SevenLaneClaimBoundary
