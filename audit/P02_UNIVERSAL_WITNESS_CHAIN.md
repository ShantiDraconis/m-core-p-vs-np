# P02 Universal Witness Chain

Status: INTEGRATION SOURCE / OPEN_MATH PRODUCER PRESERVED

This file makes the existing separation-witness chain explicit without adding
any new mathematical assumption.

## Canonical chain

```text
MCore.SeparationWitnessData                         [existing K10 payload]
        |
        | k10DataToUniversalWitness
        v
MCore.Real.P02WitnessChain.UniversalWitness        [alias of LowerBoundWitness]
        |
        | Nonempty
        v
UniversalWitnessExists                             [OPEN_MATH producer]
        |
        | universalWitnessExists_iff_g21PointwiseCore
        v
G21PointwiseCore                                   [same fixed-model lower bound]
        |
        | g21PointwiseCore_to_p02TargetCore
        v
P02TargetCore                                      [separation endpoint]
```

## Existing sources reused

- `lean/MCore/K10.lean`
  - `SeparationWitnessData`
  - `separation_witness_not_in_P`
  - `separation_witness_separates`
  - `k10_open_obligation`
- `lean/MCore/BackwardAudit/OrientedWitnessBoundary.lean`
  - `LowerBoundWitness`
  - `LowerBoundWitness.toSeparationWitness`
  - `typeB_closes_separation`
- `audit/EndpointCompression.lean`
  - historical `FixedWitness`
  - historical `FixedK10WitnessData`
  - `F2_FixedK10WitnessExistence`
  - `fixed_k10_to_witness`
  - `fixed_witness_implies_final`
  - `endpoint_compression`
- `audit/FinalEndpoint.lean`
  - historical final separation statement and firewall.
- `audit/ORIENTED_WITNESS_BOUNDARY.md`
  - records that the substantive missing payload is a genuine `not_in_p` proof.

## Adapter policy

The new importable file
`lean/MCore/Real/P02UniversalWitnessChain.lean` does not claim that
`UniversalWitnessExists` is inhabited. It only proves the downstream
equivalences/composition.

The exact terminal producer remains:

```lean
UniversalWitnessProducer C
= UniversalWitnessExists C
= Nonempty (LowerBoundWitness C.inP C.inNP)
```

Equivalently, for a fixed classical model, one must produce a language `L`
with both:

```lean
C.inNP L
¬ C.inP L
```

No C12 finite evidence, diagonalization label, metadata, or endpoint wiring is
accepted as a substitute for this producer.

## Promotion rule

This lane may be promoted from OPEN_MATH only after a kernel-checked term of
`UniversalWitnessProducer C` exists for the intended fixed official model,
with no `sorry`, `admit`, hidden axiom/oracle, circular import, or semantic
weakening.
