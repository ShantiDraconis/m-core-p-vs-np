# P02 final compression — 2026-10-01

Branch: `atk/p02-only-20261001`

## Reused material

Source P01 closure:
- source SHA: `4cc78949ca812817627d3867b1328cd950156353`
- theorem:
  `MCore.Real.P01RawClosureFinal.p01ConstructionGap_closed :
    MCore.Real.P01FinalCertificate.P01ConstructionGap`

This closes the canonical SAT-in-NP side through
`P01FinalCertificate.construction_closes_p01`.

## New formalization

### P02 operator kernel

Commit: `128de99e408a3a20a0288d4b8dca6ab88d32b121`

File: `lean/MCore/Real/P02OperatorKernel.lean`

Defines:
- `CounterexampleOperator := PolyDTMCandidate -> BitString`
- `CounterexampleSound language op`
- `P02Producer language`
- `CanonicalSATP02Producer`

Proves:
- `p02Producer_iff_failureGenerator`
- `p02Producer_iff_universalFailure`
- `canonicalSATProducer_iff_notInP`

Thus the operator target is definitionally tied to the existing canonical
lower-bound boundary and does not weaken it.

### Final compression

Commit: `4e1b1eb91feae9de63bd11e6e6d2d7c89da8ca0f`

File: `lean/MCore/Real/P02FinalCompression.lean`

Proves:
- `p01_closed`
- `canonical_sat_in_np`
- `canonical_p02_operator_closes`
- `final_open_math_iff_sat_not_in_p`
- `final_open_math_closes`

Canonical remaining proposition:

```
FINAL_OPEN_MATH :=
  Nonempty CanonicalSATP02Producer
```

Equivalent proposition:

```
FINAL_OPEN_MATH <->
  not InP (SATBits circuitBitEncoding)
```

## Status

- P01 material construction: PRODUCED / REUSED
- SAT-in-NP side: DERIVABLE FROM P01
- terminal composition: BUILT
- P02 operator interface: BUILT
- genuine counterexample operator inhabitant: OPEN_MATH
- unconditional P != NP endpoint: NOT ISSUED

No finite benchmark, lower-bound field projection, arbitrary encoder,
external oracle, or renamed endpoint is counted as an inhabitant.
