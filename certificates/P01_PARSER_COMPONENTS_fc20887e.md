# P01 Parser Components Certificate

Status: GREEN / FROZEN PREFIX ONLY

Source SHA: fc20887e556091a4775080ab23ee1ff61917040e
Frozen branch: frozen/p01-parser-components-green-fc20887e
ATK P01 clean run: 35700922856 — SUCCESS
Repository certificate run: 35700922859 — SUCCESS

Certified scope:
- exact canonical decoder inverse;
- exact slotAccept ↔ canonical decode semantics;
- fixed-alphabet finite-control VAR payload consumer;
- fixed-alphabet finite-control tag consumer;
- parser tape layout and initialization;
- tombstone slot-log semantics and machines;
- concrete parserMachine : TM (Fin 25) (Option Bool);
- initialization/path/budget source chain;
- fail-closed source hygiene and axiom audits;
- exact P02 terminal frontier statement.

Explicitly NOT certified by this prefix:
- Nonempty SlotParserMachineSimulationCertificate;
- CanonicalRecursiveParserOperationalGap;
- CanonicalSATMachineClosure / P01 final;
- P02 universal SAT lower bound;
- P ≠ NP.

Promotion remains fail-closed until the missing terminal producers are kernel checked.
