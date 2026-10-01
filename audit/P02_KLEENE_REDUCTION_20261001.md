# P02 Kleene reduction — 2026-10-01

Branch: `atk/p02-only-20261001`
Commit: `e6e8ac8eaff800ad2ace4ae7d4239afd8f6cf1c6`

## New kernel layer

File:
`lean/MCore/Real/P02KleeneKernel.lean`

The module introduces:

- `DeclaredAccept M x`
- `EffectiveDiagonalCompiler M`
- `SATFixedPointRealizer M K`
- `KleeneSATBridge`
- `KleeneSATBridgeGap`

It reuses Mathlib's recursion theorem:

`Nat.Partrec.Code.fixed_point₂`

and proves mechanically:

```
semantic flip at a recursion-theorem fixed point
  -> not CorrectAt
  -> CanonicalSATP02Producer
  -> not InP SATTarget
```

Key theorems:

- `kleene_fixed_point`
- `fixed_flip_fails`
- `KleeneSATBridge.toP02Producer`
- `kleene_bridge_closes_p02`
- `kleene_bridge_closes_not_in_p`

## Exact remaining construction

```
structure KleeneSATBridge where
  compiler : forall M, EffectiveDiagonalCompiler M
  realizer : forall M, SATFixedPointRealizer M (compiler M)
```

No lower-bound conclusion is stored in this structure.

The remaining semantic obligation is to construct an effective diagonal
compiler and prove that its recursion-theorem fixed point is represented by a
canonical SAT bitstring whose SAT truth value is the opposite of the
candidate's declared acceptance bit on that same bitstring.

## Status

P01 = PRODUCED
SAT_IN_NP = DERIVED
KLEENE_FIXED_POINT = PROVED/REUSED
FIXED_POINT_FLIP_TO_FAILURE = PROVED
P02_OPERATOR_EXTRACTION = PROVED
KLEENE_SAT_BRIDGE = OPEN_MATH
P02 / SAT_NOT_IN_P = OPEN_MATH
