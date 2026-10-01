# ATK Material Unification V2 — P vs NP

Authoritative material terminal shape: a concrete canonical-model language `L`
with an independently constructed `InNP L` witness and an operational
`FailureGenerator L`.

`¬ InP L` is a theorem derived from the generator via
`failure_generator_implies_universal_failure` and
`universal_failure_implies_not_in_p`; it is not permitted as an input field.

Transport types such as `LowerBoundWitness` and `CanonicalNotInPWitness` remain
valid downstream adapters but cannot count as material producers.

Current exact residue: construct
`CanonicalFailureProducer.failure_generator` without endpoint-equivalent
premises. Status: OPEN_MATH.