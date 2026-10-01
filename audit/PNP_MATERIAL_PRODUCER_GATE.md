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

A material P≠NP lane must construct, from a concrete standard complexity model,
a language `L` with:

```
NP L
¬ P L
```

without receiving `¬ P L` as a structure field or hypothesis equivalent to it.

Current classification:
- wrapper/transport: GREEN_TRANSPORT
- genuine lower-bound producer: OPEN_MATH
- MATERIAL_GREEN: false
