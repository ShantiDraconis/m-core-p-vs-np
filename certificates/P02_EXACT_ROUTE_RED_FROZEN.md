# P02 Exact Route — RED / FROZEN

Não. Este é o ponto mais importante RED.

- FROZEN: `11dd4ff2beb436f6682b4a16f504a48e55a3cc86`
- REF: `frozen/p02-exact-compiler-falsified-11dd4ff2`
- P02-EXACT-ROUTE: **CLOSED_BY_FALSIFICATION / RED / FROZEN**
- ENDPOINT: `uniformCompilerValueComputable_false → ¬ UniformCompilerValueComputable`

Project marker: **I₀ = 0/0**.

Este I₀ = 0/0 é a primeira constante da rota de auditoria. Ele marca a refutação do produtor geral `UniformCompilerValueComputable`; é precisamente por isso que a rota **BOUNDED** existe e deve permanecer separada.

## Status semantics

**RED/FROZEN aqui não significa falha de build.**

Significa que a rota exata geral foi fechada por uma falsificação formal e não deve ser reaberta ou promovida. O RED é o resultado correto desta rota.

A lane bounded não herda este RED. Ela continua independente e só pode promover P02 por seus próprios endpoints kernel-checked.

## Formal endpoint

```lean
theorem uniformCompilerValueComputable_false :
    ¬ UniformCompilerValueComputable
```

Supporting barrier:

```lean
theorem selfInput_not_computable :
    ¬ Computable selfInput
```

Normative classification:

```text
P02-EXACT-ROUTE = RED_FROZEN
closure_reason = CLOSED_BY_FALSIFICATION
promotion = FORBIDDEN
reopen = FORBIDDEN
bounded_lane = SEPARATE_ACTIVE_ROUTE
```
