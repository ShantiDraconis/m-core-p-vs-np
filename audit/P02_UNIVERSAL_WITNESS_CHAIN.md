# P02 Universal Witness Integrated Chain

Status: **INTEGRATED SOURCE / OPEN_MATH PRODUCER PRESERVED**

## Provenance reused

- frozen source: `frozen/p02-g2-2-wiring-green-38db71b4`
- source SHA: `38db71b416906e5b7138774842e91d3e367aad09`
- certified G2.2 run: `35722282451`
- semantic diagonal snapshot: `f29f5984a92d7681887801e50ec2b6143d9f7ee4`
- literal fixed-point firewall: `26e721ab25425d62312945200baa9c127910d320`
- literal fixed-point countermodel: `9d6dd9575a61782c70137abff348356f805bc654`
- canonical normalization: `d72e53bc7f667c75a432226a23adc59a255c5652`

The complete 58-module `lean/MCore/Real` dependency snapshot from the G2.2
frozen lane is imported into the integration branch so the P02 endpoint is
buildable as one graph rather than as detached historical files.

## Exact canonical chain

```text
UniversalWitness
  = FailureGenerator SATTarget
        |
        | Nonempty
        v
UniversalWitnessExists / UniversalWitnessProducer     OPEN_MATH
        |
        | iff
        v
G21Pointwise
  = forall PolyDTMCandidate, exists x, not CorrectAt SATTarget x
        |
        | iff
        v
P02Target
  = SATFailGap circuitBitEncoding
        |
        | iff
        v
not InP SATTarget
```

## Stronger reusable diagonal route

```text
DiagonalCounterexampleWitness M
        |
        v
DiagonalFamily
        |
        v
DiagonalFixedPointGap
        |
        v
UniversalWitnessExists
        |
        v
G21Pointwise -> P02Target
```

The semantic clocked transformer is retained because its validity, constant
length and semantic flip theorems are proved. Its literal fixed-point route is
also retained, but explicitly as a falsified sub-route:
`no_universal_literal_fixed_point`.

## K9/K10 route

K9/K10 remain connected as a generic separation route:
`SeparationWitnessData -> LowerBoundWitness -> generic separation`.
They are not silently identified with the SAT-specific G21 producer. To enter
the canonical P02 chain they must produce the fixed canonical SAT target and
its genuine `not_in_p` proof.

## Final internal endpoint

```text
SATInNPGap circuitBitEncoding
        +
UniversalWitnessExists
        |
        v
PneqNP
```

The theorem `p01_universalWitness_closes_internal` performs this final
composition conditionally. The integration does not claim an inhabitant of
`UniversalWitnessProducer`.
