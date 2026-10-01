# P02 KERNEL GREEN CERTIFICATE

Status: CERTIFIED
Scope: P02 kernel structural + Lean kernel validation only

Validated source SHA:
`fa83d082fe219a772aa41c981e6b0fa420ff2aac`

Frozen branch:
`frozen/p02-kernel-green-fa83d082`

Certificate branch:
`cert/p02-kernel-fa83d082-run36831482480`

GitHub Actions run:
`36831482480`

Artifact:
`p02-targeted-one-shot-fa83d082fe219a772aa41c981e6b0fa420ff2aac`

Artifact ID:
`11147466059`

Artifact digest:
`sha256:bdfbd8d2d4bb02e32193ee6de01deb675e27121b5ec2c8828047b76e69777ebe`

## Validated modules

- `MCore.Real.P02OperatorKernel`
- `MCore.Real.P02FinalCompression`
- `MCore.Real.P02UniversalLowerBound`
- `MCore.Real.P02UniversalKernel`
- `MCore.Real.P02KleeneKernel`
- `MCore.Real.P02EffectiveAlignment`

## Checks passed

- targeted source hygiene
- no targeted `sorry` / `admit`
- no targeted explicit `axiom` / `constant` declarations
- targeted `lake build`
- `#print axioms` audit
- no `sorryAx`
- only allowed kernel axioms:
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
- fail-closed certificate generation

## Build evidence

The run reported:

```
Built MCore.Real.P02OperatorKernel
Built MCore.Real.P02FinalCompression
Built MCore.Real.P02UniversalLowerBound
Built MCore.Real.P02UniversalKernel
Built MCore.Real.P02KleeneKernel
Built MCore.Real.P02EffectiveAlignment
[P02] GREEN: targeted validation passed
```

## Does not certify

This certificate does NOT certify:

- an inhabitant of `SemanticDiagonalFamily`
- `PointwiseSemanticDiagonal`
- an inhabitant of `FINAL_OPEN_MATH`
- the concrete P01 implementation on this branch
- final P01 + P02 composition on this HEAD
- unconditional `P != NP`

The remaining genuine open mathematics is the D3 semantic diagonal family / universal SAT lower-bound producer.
