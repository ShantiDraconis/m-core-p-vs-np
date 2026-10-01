# P vs NP MATERIAL_PRODUCER_GATE v1

The existing `LowerBoundWitness` is a conditional wrapper:

```lean
structure LowerBoundWitness (P NP : Language → Prop) where
  language : Language
  in_np : NP language
  not_in_p : ¬ P language
```

Thus `typeB_closes_separation` and `LowerBoundWitness.toSeparationWitness`
are valid transports from a supplied lower bound, but are not producers of the lower bound.

## Material requirement

A material P≠NP lane must construct, from the canonical complexity model, an
operational producer for one explicit language `L`:

```
InNP L
FailureGenerator L
```

where `FailureGenerator L` computes a concrete counterexample input for every
deterministic polynomial-time candidate and proves that the candidate is wrong
on that input.

The endpoint proposition `¬ InP L` must be **derived** from the generator.
It is forbidden as an input field, hypothesis, oracle, or equivalent wrapper.

Canonical material type:
`MCore.Attack.CanonicalFailureProducer`.

Current classification:
- `CanonicalNotInPWitness`: GREEN_TRANSPORT only
- `CanonicalFailureProducer → ¬InP`: GREEN_DERIVATION
- construction of `CanonicalFailureProducer.failure_generator`: OPEN_MATH
- MATERIAL_GREEN: false
