# P02 self-hosted runner

This runner is dedicated to the P02 Lean kernels.

Required labels:
- `self-hosted`
- `linux`
- `x64`
- `p02`
- `lean419`
- `mcore`

## Bootstrap

Generate a fresh repository Actions registration token in GitHub, then on the runner host:

```bash
export RUNNER_TOKEN='...'
export REPO_URL='https://github.com/ShantiDraconis/m-core-p-vs-np'
bash scripts/runner/bootstrap-p02-runner.sh
```

Start:

```bash
cd ~/actions-runner-p02
./run.sh
```

Or install as a service:

```bash
cd ~/actions-runner-p02
sudo ./svc.sh install
sudo ./svc.sh start
sudo ./svc.sh status
```

The bootstrap installs Elan and pins `leanprover/lean4:v4.19.0`.
The priority workflow runs both:
- `MCore.Real.P02UniversalFailureWitnessMaterial`
- `MCore.Real.P02SequentialCompositionMachine`

No `sorry`, `admit`, source-level `axiom`, or `sorryAx` is accepted.
