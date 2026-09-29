# P01 ENCODED EVALUATOR — GREEN FROZEN

Status: **GREEN_FROZEN_REDUCTION**
Scientific status: **OPEN_IMPLEMENTATION**

Frozen source:
- SHA: `62956cc7760834d80bae27e5b928d06d92334a62`
- Branch: `frozen/p01-encoded-evaluator-green-62956cc7`
- Workflow: `ATK P01 encoded evaluator`
- Run: `36508360906` — SUCCESS

## Certified content

`MCore.Real.P01EncodedEvaluator.evalEncodedCore` evaluates the canonical
prefix bit encoding directly, without constructing a `Circuit` value in
finite control.

Kernel-checked theorems:
- `evalEncodedCore_encode_append`
- `evalEncoded_encode`
- `evalEncoded_witness`

The evaluator preserves the unconsumed tail and agrees exactly with
`evalCircuit` on `encodeCircuit c`.

## What this removes from P01

The semantic decode/evaluation map is no longer an open obligation.
A future physical verifier does not need to postulate an AST decoder: it can
refine this streaming bit evaluator directly.

## Remaining material work

1. Refine the streaming evaluator into one fixed finite-control TM using the
   already-certified physical stack, witness-read and movement primitives.
2. Prove global polynomial halting and physical/logical equivalence.
3. Compose parser + fixed witness guesser + physical verifier into one
   `P01MachineConstruction`.

This certificate does not inhabit `P01MachineConstruction` and does not
establish `G21Pointwise`.
