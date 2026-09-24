# Prime2 research lane for FINAL_PROOF

Status: RESEARCH_ONLY / ZERO_PROOF_CREDIT

Purpose: investigate whether an experimental arithmetic/model with an alternative Prime2 notion can yield a semantic failure theorem that transfers conservatively into the existing standard P-vs-NP formalization.

## Allowed terminal bridge

The only admissible promotion path is:

Prime2ResearchClosure
-> Prime2SemanticFailureTransfer
-> G21Pointwise
-> P02Target
-> existing FINAL_PROOF chain.

The research lane does not redefine G21Pointwise, P02Target, SATTarget, PolyDTMCandidate, OfficialPneqNP, or FinalExternalCertificate.

## Mandatory research gaps

R-P2.1 ConservativeInterpretationGap
Construct a real ConservativePrime2Interpretation.

R-P2.2 MappedPrime2UniversalFailure
For every real PolyDTMCandidate M, produce a standard BitString x such that the mapped experimental candidate fails on the mapped x.

## Fail-closed firewall

No proof credit until both R-P2.1 and R-P2.2 are inhabited and kernel-checked.

No axiom, sorry, admit, oracle, fabricated fixed point, or P012 status label may discharge either gap.

The experimental claim that there are multiple even primes is not imported into standard arithmetic. Any useful consequence must pass through the conservative interpretation.

## Final target

The only accepted final output of this route is the existing theorem:

G21Pointwise :=
  forall candidate : PolyDTMCandidate,
    exists x : BitString,
      not candidate.CorrectAt SATTarget x

If that theorem is obtained through the conservative transfer, the normal downstream wiring may consume it.
