# P01 EVAL-FRAME POP/READ MACHINE — GREEN FROZEN

Status: **GREEN_FROZEN_PHYSICAL_SUBROUTINE**
Scientific status: **OPEN_IMPLEMENTATION**

Frozen source:
- SHA: `7f6597a14f0fcdfd7ee53edb880dd797748d5646`
- Branch: `frozen/p01-frame-pop-read-green-7f6597a1`
- Workflow: `ATK P01 encoded evaluator`
- Run: `36540846559` — SUCCESS

Certified physical behavior:
- one fixed TM `framePopMachine`;
- consumes exactly one three-bit `EvalFrame` code from the canonical V2 stack;
- decodes the frame entirely in finite control;
- erases exactly those three physical cells and restores the canonical blank-head layout;
- proves exact tape equality and `PhysicalStackRepV2` preservation;
- rejects the deliberately unused code `111`;
- build, axiom audit, and proof-escape scan are GREEN.

Certified theorems:
- `framePop_run_four`
- `framePop_run_four_rep`
- `framePop_rejects_111`

Together with frozen `framePushMachine`, physical push/pop/read of the fixed-width
three-bit evaluator-frame stack is now closed.

Remaining P01 material frontier:
1. refine each frozen semantic `evalStep` transition to the physical tape;
2. prove global physical verifier halting/correctness against frozen `evalRun`;
3. compose parser + witness guesser + physical verifier into one `P01MachineConstruction`.

This certificate does not inhabit `P01ConstructionGap` and does not affect `G21Pointwise`.
