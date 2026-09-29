# P01 EVALSTEP FRAME REFINEMENT — GREEN FROZEN

Status: **GREEN_FROZEN_SUBGATE**
Scientific status: **P01 OPEN_IMPLEMENTATION**
P-vs-NP status: **OPEN_MATH**

Frozen source:
- SHA: `8e3abccc052e631346f9decbf4db0c601080fde6`
- Branch: `frozen/p01-evalstep-frame-refinement-green-8e3abccc`
- Certificate run: `36542400193` — SUCCESS

## Kernelized content

Module:
`MCore.Real.P01EvalStepFrameRefinement`

Certified physical refinements:
- semantic frame push ↔ three physical TM steps;
- semantic frame pop/read ↔ four physical TM steps;
- NOT/AND/OR tag transitions push the exact canonical `EvalFrame`;
- NOT return pops `.neg` and leaves Boolean result in finite control;
- AND-left / OR-left return performs certified pop then certified push of
  `.andRight l` / `.orRight l`;
- AND-right / OR-right return pops the stored finite frame and computes the
  Boolean result in finite control;
- every `EvalFrame` head is physically decodable/removable fail-closed.

The CI explicitly performed:
- targeted build `MCore.Real.P01EvalStepFrameRefinement`: GREEN;
- axiom audit of all new refinement theorems: GREEN;
- repository proof-escape hygiene: GREEN.

## What this removes from the frontier

The following are no longer open P01 obligations:
- physical encoding of EvalFrame;
- physical EvalFrame push;
- physical EvalFrame pop/read;
- frame-stack effects of NOT/AND/OR tag transitions;
- frame-stack effects of all semantic return transitions.

## Exact remaining P01 implementation frontier

1. Construct a single physical source-cursor ↔ stack-end invariant/shuttle that
   preserves the unread canonical source tail while permitting the certified
   frame-stack operations.
2. Refine input/constant/tag source consumption against that physical cursor,
   reusing the already-certified indexed witness-read machine.
3. Lift the one-step refinement to the frozen `evalRun` semantics and prove
   global polynomial halting/correctness.
4. Compose parser + `witnessGuessMachine` + physical verifier into one
   `P01MachineConstruction`.

This certificate does **not** inhabit `P01MachineConstruction`, does not prove
`G21Pointwise`, and does not prove P != NP.
