# P01 bounded verified relation — GREEN

- Repository: `ShantiDraconis/m-core-p-vs-np`
- Source SHA: `1453539c13ba5224d1b84198f162075741a12a98`
- Frozen ref: `frozen/p01-verified-relation-green-1453539c`
- Dedicated run: `35587134807` — SUCCESS
- Repository certificate run: `35587134861` — SUCCESS
- Repository fail-proof-all-gaps run: `35587134839` — SUCCESS
- File: `lean/MCore/Real/P01VerifiedRelation.lean`
- Classification: `FROZEN_POSITIVE_PREFIX`
- Progress metric: **NOT** a `FROZEN_HARD`

## Certified positive prefix

For the canonical circuit bit encoding, `SATBits x` is kernel-proved
equivalent to existence of a decoded circuit together with a finite witness
accepted by the certified verifier.  The witness bit-length is bounded by the
canonical circuit encoding length.

On canonical encodings this specializes exactly to the existing
`SATLanguage` statement.

## Remaining P01 obligation

This theorem is verifier semantics, not yet the repository's hardened
single-tape nondeterministic machine realization.  P01 remains open until a
concrete polynomial-time parser/guess/verifier machine is composed into
`PolyNTMRealization (SATBits circuitBitEncoding)`.

P02 (`SAT ∉ P`) remains entirely separate and open.
