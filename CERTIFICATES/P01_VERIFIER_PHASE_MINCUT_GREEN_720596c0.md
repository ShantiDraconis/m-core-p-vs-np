# P01 VERIFIER PHASE MIN-CUT — GREEN FROZEN CERTIFICATE

Status: **GREEN_FROZEN_CERTIFIED**
Scientific status: **P01 MECHANICAL MIN-CUT CLOSED**
P-vs-NP status: **NOT PROMOTED BY THIS CERTIFICATE**

Frozen source:
- SHA: `720596c0bd3900b5de25eab57b7b979d2a6aaf68`
- Branch: `frozen/p01-verifier-phase-mincut-green-720596c0`
- Certificate ref: `cert/p01-verifier-phase-mincut-green-720596c0`
- Authoritative workflow: `P01 Verifier Phase Min-Cut Clean`
- Workflow run: `36862291065` — SUCCESS
- Authoritative job: `110369170512`

Parallel validation on the same SHA:
- `certificate` run `36862291133` — SUCCESS
- `fail-proof-all-gaps` run `36862292228` — SUCCESS

## Passed gates

- dependency resolution
- complete structural min-cut build
- `MCore.Real.P01RawRecursiveSteps`
- `MCore.Real.P01RawDecodeInduction`
- `MCore.Real.P01RawTotalizationProducer`
- `MCore.Real.P01VerifierPhaseMinCutStructural`
- exact axiom audit
- placeholder firewall
- no `sorry`, `admit`, `sorryAx`, or prohibited local axiom/constant declarations in the certified final lane

## Kernelized closure

The certified lane contains the concrete raw-totalization producer:

```lean
MCore.Real.P01RawTotalizationProducer.rawDecodeNoneFailClosedProducer :
  RawDecodeNoneFailClosed
```

and its closure theorem:

```lean
MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed :
  P01FinalCertificate.P01ConstructionGap
```

The structural verifier-phase bridge also kernel-checks:

```lean
MCore.Real.P01VerifierPhaseMinCutStructural.p01ConstructionGap_of_verifierPhase
```

## Frozen scope

The following mechanical chain is frozen and should be reused, not recomputed:

`P01RawRecursiveSteps -> P01RawDecodeInduction -> P01RawTotalizationProducer -> P01VerifierPhaseMinCutStructural`.

This certificate records the verified P01 mechanical construction gap closure at the stated SHA. It does not by itself certify the independent asymptotic lower-bound / SAT-not-in-P obligation and therefore does not by itself establish P != NP.

## Advance rule

Further work must branch forward from the frozen SHA and preserve this checkpoint unchanged.
