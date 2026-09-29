# P01 ENCODED STACK EVALUATOR — GREEN FROZEN

Status: **GREEN_FROZEN_REDUCTION**
Scientific status: **OPEN_IMPLEMENTATION**

Frozen source:
- SHA: `f70ab88b3ac8cb1bd37c5e6f3115e26184b39b2b`
- Branch: `frozen/p01-encoded-stack-evaluator-green-f70ab88b`
- Workflow: `ATK P01 encoded evaluator`
- Run: `36508950379` — SUCCESS

## Certified content

The canonical prefix encoding is evaluated by an explicit finite-frame
small-step machine semantics:

- finite frame alphabet `EvalFrame`;
- explicit state `EvalState = bits × frame-stack × optional-value`;
- one-step transition `evalStep`;
- iterative execution `evalRun`;
- exact continuation theorem `evalRun_encode_append`;
- linear semantic control bound
  `evalStepCount c ≤ 3 * (encodeCircuit c).length`;
- bounded final theorem `evalRun_encode_bounded`.

No `Circuit` AST is stored in control. Recursive structure is represented
only by the finite frame alphabet and a data stack.

## Kernel audit

The CI run passed:
- kernel build;
- #print axioms audit;
- proof-escape scan.

## Remaining material P01 work

Refine this finite-frame semantics into one fixed finite-control physical TM
over the canonical `Option Bool` tape, using the already-certified physical
stack, witness-read, movement, source-rewind and polynomial-budget primitives.
Then compose parser + fixed witness guesser + that verifier into one
`P01MachineConstruction`.

This certificate does not inhabit `P01MachineConstruction` and does not
establish `G21Pointwise`.
