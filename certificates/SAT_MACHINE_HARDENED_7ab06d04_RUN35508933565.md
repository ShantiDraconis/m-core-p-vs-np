# SAT realization — hardened machine interface GREEN certificate

- Repository: `ShantiDraconis/m-core-p-vs-np`
- Certified source SHA: `7ab06d0430e48a323b1ed0096abe97762303c893`
- Frozen ref: `frozen/sat-machine-hardened-green-7ab06d04`
- Certificate ref: `cert/sat-machine-hardened-7ab06d04-run35508933565`
- Workflow run: `35508933565`
- Job: `106073346075` (`c12`)
- Result: **GREEN / SUCCESS**
- Artifact: `pnp-closed-chain-data` id `10604828269`
- Artifact digest: `sha256:064c21cb19dea59dfd91d515289f7f9244097387adda02d31ead19e8c7e33d5a`

## Certified scope

This successor hardens the SAT-machine interface by requiring every encoded input configuration to start in the fixed machine control state:
`(R.encode φ).state = R.machine.initial`.

This prevents an input-dependent control state from smuggling computation into the encoding. The existing NTM model, SAT semantics, decision contract, targeted build and axiom audit remain GREEN.

## Frontier

No inhabitant of `SATMachineRealization` is constructed here. The next substantive obligation is a concrete fixed NTM and tape encoding, with uniform halting/correctness and then the required polynomial runtime / classical complexity transfer. No P-vs-NP endpoint is promoted.
