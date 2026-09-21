import MCore.Real.CanonicalSATSlotLog
import MCore.Real.CanonicalSATSlotParserSpec

namespace MCore
namespace Real
namespace CanonicalSATParserMachine

open CanonicalFinalProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog

/-
State map (Fin 31):
 0 INIT_SCAN_RIGHT
 1 INIT_WRITE_SLOT
 2 INIT_CROSS_DELIM
 3 INIT_REWIND
 4 TAG_0
 5 TAG_AFTER_0
 6 TAG_AFTER_1
 7 TAG_AFTER_00
 8 TAG_AFTER_01
 9 TAG_AFTER_10
10 VAR_LOOP
11 LEAF_SEEK_DELIM
12 UNARY_SEEK_DELIM
13 BINARY_SEEK_DELIM
14 LEAF_SCAN_LOG_END
15 UNARY_SCAN_LOG_END
16 BINARY_SCAN_LOG_END
17 LEAF_POP_SEARCH
18 UNARY_POP_SEARCH
19 BINARY_POP_SEARCH
20 LEAF_CHECK_ACTIVE_LEFT
21 LEAF_RETURN_ACTIVE_DELIM
22 UNARY_GO_END
23 CROSS_INPUT_ACTIVE
24 CROSS_INPUT_ZERO
25 RETURN_DELIM_ACTIVE
26 BINARY_GO_END
27 BINARY_PUSH_SECOND
28 REWIND_INPUT_ACTIVE
29 ACCEPT
30 REJECT
-/

def parserMachine : TM (Fin 31) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some b => (0, some b, .right)
        | none => (1, none, .right)
      else if q = 1 then
        (2, some true, .left)
      else if q = 2 then
        (3, symbol, .left)
      else if q = 3 then
        match symbol with
        | some b => (3, some b, .left)
        | none => (4, none, .right)
      else if q = 4 then
        match symbol with
        | none => (30, none, .stay)
        | some false => (5, none, .right)
        | some true => (6, none, .right)
      else if q = 5 then
        match symbol with
        | none => (30, none, .stay)
        | some false => (7, none, .right)
        | some true => (8, none, .right)
      else if q = 6 then
        match symbol with
        | none => (30, none, .stay)
        | some false => (9, none, .right)
        | some true => (30, none, .right)
      else if q = 7 then
        match symbol with
        | none => (30, none, .stay)
        | some false => (10, none, .right)
        | some true => (11, none, .right)
      else if q = 8 then
        match symbol with
        | none => (30, none, .stay)
        | some false => (11, none, .right)
        | some true => (12, none, .right)
      else if q = 9 then
        match symbol with
        | none => (30, none, .stay)
        | some _ => (13, none, .right)
      else if q = 10 then
        match symbol with
        | none => (30, none, .stay)
        | some true => (10, none, .right)
        | some false => (11, none, .right)
      else if q = 11 then
        match symbol with
        | some b => (11, some b, .right)
        | none => (14, none, .right)
      else if q = 12 then
        match symbol with
        | some b => (12, some b, .right)
        | none => (15, none, .right)
      else if q = 13 then
        match symbol with
        | some b => (13, some b, .right)
        | none => (16, none, .right)
      else if q = 14 then
        match symbol with
        | some b => (14, some b, .right)
        | none => (17, none, .left)
      else if q = 15 then
        match symbol with
        | some b => (15, some b, .right)
        | none => (18, none, .left)
      else if q = 16 then
        match symbol with
        | some b => (16, some b, .right)
        | none => (19, none, .left)
      else if q = 17 then
        match symbol with
        | some false => (17, some false, .left)
        | some true => (20, some false, .left)
        | none => (30, none, .stay)
      else if q = 18 then
        match symbol with
        | some false => (18, some false, .left)
        | some true => (22, some false, .right)
        | none => (30, none, .stay)
      else if q = 19 then
        match symbol with
        | some false => (19, some false, .left)
        | some true => (26, some false, .right)
        | none => (30, none, .stay)
      else if q = 20 then
        match symbol with
        | some false => (20, some false, .left)
        | some true => (21, some true, .left)
        | none => (24, none, .left)
      else if q = 21 then
        match symbol with
        | some b => (21, some b, .left)
        | none => (23, none, .left)
      else if q = 22 then
        match symbol with
        | some b => (22, some b, .right)
        | none => (25, some true, .left)
      else if q = 23 then
        match symbol with
        | none => (30, none, .stay)
        | some b => (28, some b, .left)
      else if q = 24 then
        match symbol with
        | none => (29, none, .stay)
        | some b => (30, some b, .stay)
      else if q = 25 then
        match symbol with
        | some b => (25, some b, .left)
        | none => (23, none, .left)
      else if q = 26 then
        match symbol with
        | some b => (26, some b, .right)
        | none => (27, some true, .right)
      else if q = 27 then
        (25, some true, .left)
      else if q = 28 then
        match symbol with
        | some b => (28, some b, .left)
        | none => (4, none, .right)
      else
        (q, symbol, .stay)
    halting := fun q => (q == 29) || (q == 30) }

@[simp] theorem parserMachine_blank_none :
    parserMachine.blank = none := rfl

def parserAccepting : Fin 31 → Bool :=
  fun q => q == 29

@[simp] theorem parserAccepting_accept :
    parserAccepting 29 = true := by decide

@[simp] theorem parserAccepting_reject :
    parserAccepting 30 = false := by decide

@[simp] theorem parserMachine_halts_accept :
    parserMachine.halting 29 = true := by decide

@[simp] theorem parserMachine_halts_reject :
    parserMachine.halting 30 = true := by decide

@[simp] theorem parserMachine_not_halted_tag0 :
    parserMachine.halting 4 = false := by decide

/-- Conservative global budget for the eventual macro-simulation proof. -/
def parserTimeBound : TimeBound :=
  fun n => 256 * (n + 1) ^ 2

theorem parserTimeBound_poly :
    PolynomialTimeBound parserTimeBound := by
  refine ⟨256, 2, ?_⟩
  intro n
  exact Nat.le_refl _

/-- Type-level finite-control/fixed-alphabet firewall. -/
theorem parserMachine_has_canonical_type :
    Nonempty (TM (Fin 31) (Option Bool)) :=
  ⟨parserMachine⟩

/-- The chosen literal state count for CanonicalRecursiveParserMachineCertificate. -/
def parserStateCount : Nat := 30

theorem parserStateType :
    Fin (parserStateCount + 1) = Fin 31 := by
  rfl

/--
The machine has no semantic input parameter: its only eventual public input is
the canonical initial tape built from bits.
-/
def parserInitialConfig (bits : BitString) :
    Configuration (Fin 31) (Option Bool) :=
  initialTMConfig parserMachine bits

@[simp] theorem parserInitialConfig_state (bits : BitString) :
    (parserInitialConfig bits).state = (0 : Fin 31) := by
  rfl

#print axioms MCore.Real.CanonicalSATParserMachine.parserMachine_blank_none
#print axioms MCore.Real.CanonicalSATParserMachine.parserTimeBound_poly
#print axioms MCore.Real.CanonicalSATParserMachine.parserMachine_has_canonical_type
#print axioms MCore.Real.CanonicalSATParserMachine.parserInitialConfig_state

end CanonicalSATParserMachine
end Real
end MCore
