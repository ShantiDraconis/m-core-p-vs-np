# P02 bounded same-input — RED / CLOSED_BY_FALSIFICATION

Status: RED / FROZEN / CLOSED_BY_FALSIFICATION

Formal source:
- lean/MCore/Real/P02BoundedOpenMathFalsification.lean
- source commit: 49b2ba3cf73e4d1d201e9b12bb26f4ecbfc63ad6

Kernel CI:
- workflow: P02 bounded lane
- run: 35930277832
- conclusion: SUCCESS

Kernel-checked endpoints:
- MCore.Real.P02BoundedOpenMathFalsification.rejectCircuit_strict_growth
- MCore.Real.P02BoundedOpenMathFalsification.not_BoundedSameInputEquation
- MCore.Real.P02BoundedOpenMathFalsification.not_UniformBoundedSameInputProducer

Closure:
RejectStrictGrowth implies the current bounded same-input equation is impossible.
This is a route falsification only. It is not positive evidence for P02Target and
must not be promoted into FinalExternalInputs.

Normative separation:
- exact same-input route remains independently RED/FROZEN at 11dd4ff2beb436f6682b4a16f504a48e55a3cc86
- semantic-stability lane remains the active P02 route
