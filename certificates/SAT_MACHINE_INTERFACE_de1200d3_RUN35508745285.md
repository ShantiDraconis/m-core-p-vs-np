# SAT realization — machine interface GREEN certificate

- Repository: `ShantiDraconis/m-core-p-vs-np`
- Certified source SHA: `de1200d3161b22bc0d812f3910a1764307dcb732`
- Frozen ref: `frozen/sat-machine-interface-green-de1200d3`
- Certificate ref: `cert/sat-machine-interface-de1200d3-run35508745285`
- Workflow run: `35508745285`
- Job: `106072858370` (`c12`)
- Result: **GREEN / SUCCESS**
- Artifact: `pnp-closed-chain-data` id `10604787896`
- Artifact digest: `sha256:993f09d5ae372f103541d0192c67272374f28e6c26d1d5557c726818f72588e6`

## Certified scope

This checkpoint reuses the repository's existing NTM model and adds the typed decision contract `NTM.DecidesWithin`, the existing-Circuit SAT language, and the explicit `SATMachineRealization` witness package. The targeted module build and axiom audit are GREEN.

## Frontier

The interface does not construct an inhabitant of `SATMachineRealization`. The next mathematical/formal obligation is an actual fixed NTM/encoding/time bound with a proof of halting and SAT correctness on every input, followed by the required polynomial-bound and classical complexity transfer. No P-vs-NP endpoint is promoted.
