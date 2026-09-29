# P01 FIVE-TAG CURSOR REFINEMENT — GREEN FROZEN

Status: **GREEN_FROZEN_PHYSICAL_REFINEMENT**
Scientific status: **P01 OPEN_IMPLEMENTATION**

Frozen source:
- SHA: `6707aa0e65781e9d5674414bbf6c930443531bba`
- Branch: `frozen/p01-five-tag-cursor-refinement-green-6707aa0e`
- Workflow: `ATK P01 encoded evaluator`
- Run: `36552792426` — SUCCESS

## Kernelized content

The physical cursor evaluator now refines all five finite three-bit tags:

- `001` — constant false;
- `010` — constant true;
- `011` — NOT, including exact `.neg` frame push;
- `100` — AND, including exact `.andLeft` frame push;
- `101` — OR, including exact `.orLeft` frame push.

Certified declarations:
- `consumeThree_then_push_frame`
- `evalStep_const_false_cursor_refined`
- `evalStep_const_true_cursor_refined`
- `evalStep_not_tag_cursor_refined`
- `evalStep_and_tag_cursor_refined`
- `evalStep_or_tag_cursor_refined`

The same run also kernel-builds the corrected
`P01SourceCursorInvariant.moveToSourceStart_head_correct`.

## Exact remaining local evalStep case

Only the input-node case remains locally unrefined:

```text
000 ++ encodeNat(i)
```

The existing `witnessIndexedReadMachine` is fixed-control and correct, but it
destructively consumes witness-prefix cells while counting.  Therefore it is
not sufficient for a global evaluator where the same assignment variable can
be read more than once.

The next admissible local producer is a fixed finite-control **preserving unary
indexed witness reader** which:
1. consumes the unary index as tape data;
2. returns the selected witness bit;
3. restores the witness region exactly;
4. preserves the unread source tail and frame stack.

DOES_NOT_CERTIFY:
- the input-node refinement;
- global physical `evalRun`;
- `P01MachineConstruction`;
- `P01ConstructionGap`;
- `G21Pointwise`;
- P != NP.
