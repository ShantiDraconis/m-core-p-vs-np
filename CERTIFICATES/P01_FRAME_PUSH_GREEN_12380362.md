# P01 EVAL-FRAME PUSH MACHINE — GREEN FROZEN

Status: **GREEN_FROZEN_PHYSICAL_SUBROUTINE**
Scientific status: **OPEN_IMPLEMENTATION**

Frozen source:
- SHA: `123803627c2157d41686471dc8c2c5c96eb408ae`
- Branch: `frozen/p01-frame-push-green-12380362`
- Workflow: `ATK P01 encoded evaluator`
- Run: `36509879658` — SUCCESS

Certified physical behavior:
- one fixed TM `framePushMachine`;
- starts from a frame-specific finite-control entry state;
- writes exactly three physical frame-code bits in three steps;
- final V2 stack prefix is exactly `encodeEvalFrame f ++ stack`;
- reuses the certified `pushStep_correct` physical-stack invariant;
- rejects instead of overwriting a nonblank entry cell.

The full verifier remains OPEN: frame pop/read, global evalStep refinement,
global halting/correctness and final P01 integration are still required.
