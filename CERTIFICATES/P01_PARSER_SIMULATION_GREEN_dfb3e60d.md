# P01 Parser Simulation — GREEN / FROZEN

Scope: T1/P01 parser subgate only. This is not a P vs NP proof and does not
inhabit P01MachineConstruction.

- Frozen SHA: `dfb3e60dc37e96f46a3ca071c428456634ec6dca`
- Frozen branch: `frozen/p01-parser-simulation-green-dfb3e60d`
- Workflow: `atk-targeted`
- Run: `35790493696`
- Conclusion: `SUCCESS`

Kernel-checked terminal theorem:

```lean
MCore.Real.P01GlobalParserBound.slot_parser_machine_simulation_certificate :
  MCore.Real.CanonicalSATRecursiveParserSimulation.SlotParserMachineSimulationCertificate
```

The same compiled source proves:
- exact/global parser semantics;
- explicit proof-side runtime budget;
- `parserProofBudget bits ≤ parserTimeBound bits.length`;
- total halting at the frozen `parserTimeBound`;
- exact `slotAccept` semantics at that same fuel.

DOES_NOT_CERTIFY:
- `Nonempty P01MachineConstruction`;
- a full fixed physical verifier;
- the integrated parser → witness → verifier NTM;
- `G21Pointwise`;
- P ≠ NP.

Forward-only rule: do not reopen parser semantic/runtime construction. Downstream
P01 work must consume this certificate and attack the remaining integrated
machine/verifier obligations.
