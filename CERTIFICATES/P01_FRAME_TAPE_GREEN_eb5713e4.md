# P01 EVALUATOR FRAME TAPE — GREEN FROZEN

Status: **GREEN_FROZEN_REDUCTION**
Scientific status: **OPEN_IMPLEMENTATION**

Frozen source:
- SHA: `eb5713e48e84a8adbb0850d1f2c60b46a738b4f6`
- Branch: `frozen/p01-frame-tape-green-eb5713e4`
- Workflow: `ATK P01 encoded evaluator`
- Run: `36509233942` — SUCCESS

Certified content:
- seven `EvalFrame` variants have a fixed three-bit encoding;
- `decodeEvalFrame (encodeEvalFrame f) = some f`;
- the frame encoding is injective;
- complete frame stacks encode in exactly `3 * frames.length` bits;
- stack decoding round-trips exactly;
- malformed/truncated codes fail closed.

This is a direct physicalization step for the frozen finite-frame evaluator. It
does not inhabit the verifier or P01 endpoint.

Remaining frontier:
construct fixed finite-control tape operations implementing push/pop/read of
these three-bit frames, then refine `evalStep` globally and compose P01.
