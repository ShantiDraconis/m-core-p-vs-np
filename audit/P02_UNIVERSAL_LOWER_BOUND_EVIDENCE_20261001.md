# P02 universal lower bound — certified evidence matrix

Branch: `atk/p02-only-20261001`

## Historical certified evidence reused

### Semantic diagonal transformer
- SHA: `f29f5984a92d7681887801e50ec2b6143d9f7ee4`
- Run: `35710913464`
- Conclusion: SUCCESS
- Certified content reused:
  - canonical diagonal output validity;
  - constant-size semantic transformer;
  - semantic flip on a supplied input.
- Does NOT certify universal self-reference or SAT not in P.

### G2.0 normalization
- SHA: `d72e53bc7f667c75a432226a23adc59a255c5652`
- Run: `35707286302`
- Conclusion: SUCCESS
- Certified content reused:
  - explicit monomial clock normalization;
  - preservation of CorrectAt under clock extension.

### G2.2 wiring
- SHA: `38db71b416906e5b7138774842e91d3e367aad09`
- Run: `35722282451`
- Conclusion: SUCCESS
- Certified content reused:
  - G21 pointwise failure <-> P02 target;
  - contradiction consumer is not an independent producer.

### Kleene bridge
- SHA: `5f8a0aa2c6ca41d77515e3bf97bd1fa53138679d`
- Run: `35784099753`
- Conclusion: SUCCESS
- Certified content reused:
  - Mathlib fixed-point theorem wiring;
  - a supplied semantic bridge yields a diagonal family/P02.

### E1 computability audit
- SHA: `0f6bcd5243ee499dc3e182b81ea98459858b6883`
- Run: `35785227242`
- Conclusion: SUCCESS
- Certified conclusion:
  - the bare computable code-transformer component is inhabited;
  - E1 is not where the lower-bound hardness resides.

### E2 audit
- SHA: `b6b6821b337ae70ef958d461a44156d2345d3336`
- Run: `35785134353`
- Conclusion: SUCCESS

### E2 semantic/totality checkpoint
- SHA: `8218207dd3258860cdb9859a99ab677c36880d23`
- Run: `35788500754`
- Conclusion: SUCCESS
- Certified content reused:
  - not CorrectAt decomposes into declared-clock failure or semantic mismatch;
  - total candidate failure reduces to semantic mismatch;
  - semantic self-embedding is equivalent to the diagonal-family frontier.
- Does NOT certify existence of semantic self-embedding.

### Integration
- SHA: `270282a55e18588dce3e7a8a9a72db2cda277d98`
- Run: `35787562294`
- Conclusion: SUCCESS
- Certified content reused:
  - terminal wiring from universal witness/G21 to P02.

### Literal fixed-point falsification
- SHA: `17c04b62d03946aab4573894833f087ade25bc33`
- Run: `35721158651`
- Conclusion: SUCCESS
- Countermodel SHA: `9d6dd9575a61782c70137abff348356f805bc654`
- Run: `35721311898`
- Conclusion: SUCCESS
- Consequence:
  - literal string fixed-point route remains closed by falsification and is not reused.

## New source formalization on current branch

- `128de99e408a3a20a0288d4b8dca6ab88d32b121`
  P02 counterexample-operator kernel.
- `4e1b1eb91feae9de63bd11e6e6d2d7c89da8ca0f`
  final P01/P02 compression.
- `e6e8ac8eaff800ad2ace4ae7d4239afd8f6cf1c6`
  Kleene/SAT kernel.
- `72f1a84059920ba765c71315ed7257b5f1d86704`
  effective-alignment layer.
- `e824714ea50a737c73e37ce1d340759d4929c7b5`
  exact universal lower-bound semantics.
- `26c8c83f930406dcb955be6f884c9323f944bd5e`
  exact monomial-clock normal form.
- `ea9d9fac9e9136cd9d458382ae2d079fb6c8b688`
  MASTER theorem chain.

These new source commits have NOT been promoted to GREEN/CERTIFIED in this
branch because no new GitHub Actions run was launched.

## Exact terminal proposition

```
UNIVERSAL_LOWER_BOUND :=
  forall M : PolyDTMCandidate,
    exists x : BitString,
      not M.CorrectAt (SATBits circuitBitEncoding) x
```

Equivalent forms formalized in the current source:
- `not InP SATTarget`;
- nonempty canonical P02 counterexample operator;
- nonempty monomial-clock NormalizedAdversary;
- operational clock-failure-or-semantic-mismatch form.

## Remaining open mathematics

The missing inhabitant is still the universal adversarial construction itself.
Historical certificates establish the reductions and exclude invalid routes;
none of them supplies that inhabitant.
