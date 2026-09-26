# ATK terminal focus — 2026-09-23

## P01

Exact target:

`P01ConstructionGap = Nonempty P01MachineConstruction`.

Already available on the active lane:

- global parser simulation;
- parser phase certificate;
- witness-guess completeness and halting;
- witness-bound normalization;
- verifier logical semantics;
- physical scanner/control primitives;
- physical stack/refinement lemmas;
- fixed integrated state layout.

Remaining exact P01 producer:

- one fixed finite-control integrated NTM;
- full physical verifier execution theorem;
- phase composition parser -> witness -> verifier;
- global polynomial halting;
- exact `AcceptsWithin iff SATBits`.

No substitute proposition is accepted.

## P02

### Closed semantic field

`P02CookLevinFieldClosed.cook_levin_correct_for_carrier`
proves the pointwise semantic rejection/Cook-Levin field for every supplied
carrier input.

The literal-bitstring realization of that field is NOT used for self-reference,
because the universal literal fixed-point route is already refuted.

### Live same-input route

`P02ExtensionalSameInputBridge.ExtensionalSameInputCompiler` is the exact
non-literal recursion-theoretic interface:

- computable code transformer;
- extensional input representation under equality of `Code.eval`;
- compiler realization into the canonical circuit encoding;
- semantic rejection correctness.

Roger/Kleene fixed point then proves:

`same_input_at_fixed_point`
-> `DiagonalCounterexampleWitness`
-> `G21Pointwise`
-> `P02Target`.

Therefore the current P02 mathematical producer is no longer described as two
independent gaps. It is the construction of the uniform extensional compiler.

## Terminal chain

`P01ConstructionGap`
+
`UniformExtensionalSameInputCompiler`
-> `P02Target`
-> FinalExternal inputs
-> FinalExternalCertificate
-> FINAL_ROOT.

## Fail-closed state

- P01ConstructionGap: OPEN_IMPLEMENTATION
- cook_levin_correct (isolated semantic field): CLOSED_SOURCE
- uniform extensional same-input compiler: OPEN_MATH_CORE
- P02Target: BLOCKED_BY_EXTENSIONAL_COMPILER
- FINAL_ROOT: null
