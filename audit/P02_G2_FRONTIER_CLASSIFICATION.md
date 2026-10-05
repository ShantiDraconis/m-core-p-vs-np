# P02 G2 frontier classification

HEAD basis: certified P01/T5 plus canonical SAT boundary.

## Exact normal form

The following are exact reformulations of the same lower-bound obligation and
must not be counted as independent mathematical progress:

- UniversalFailure CanonicalSAT
- Nonempty (FailureGenerator CanonicalSAT)
- Nonempty TotalSemanticFailureProducer
- TotalExactDiagonalProducer (on the discovery branch)

The current branch proves the first three equivalent once the exactness audit
kernel-checks. The discovery branch already proves
TotalExactDiagonalProducer <-> UniversalFailure CanonicalSAT.

## Refuted route

SEMANTIC_NEGATION_INVARIANT_OPEN_MATH is false.

A concrete four-state polynomial-time DTM reads the second input bit. Since
encodeCircuit (.const false) = 001 and encodeCircuit (.const true) = 010, the
semantic-negation reduction flips that candidate's declared answer at every
input. Therefore no invariant point exists for that candidate.

Certified negative control:
- SHA 69ac44fcb58b32983a5f7003348f669e62f5477a
- run 37358153933
- frozen/p02-semantic-negation-invariant-refuted-69ac44fc

## Remaining research lanes

BehavioralAlignment, KleeneUniversalBridge, and OddParityMixing are admissible
only as sufficient producer routes. They are not closed producers on the
current certified branch and must not be promoted unless an inhabitant is
constructed without UniversalFailure/not-InP or an equivalent endpoint field.

Canonical OPEN_MATH remains:
UniversalFailure (SATBits circuitBitEncoding).
