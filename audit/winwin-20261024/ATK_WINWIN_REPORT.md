# ATK — Onde o "os dois lados se complementam" fecha alguma coisa — 2026-10-24

```
ATK-WINWIN: varredura de 28 repositórios | 2383 branches | 5525 blobs .lean únicos | 33 419 teoremas*
            | forma exata da proposta: (A → X) ∧ (¬A → X) ⇒ X   (caso-a-caso / win-win)
            | FECHA POR COMPLETO: FLT para primos regulares (Kummer), já em M-Core
            | GERA TEOREMAS VÁLIDOS NOS DOIS MUNDOS: M-Core ATK/ZeroClasses/MundoFora.lean
            | NÃO FECHA: RH, P≠NP, BSD, Hodge, Navier–Stokes, Yang–Mills, Beal
            | motivo verificado no kernel: missing_half_iff_target (este branch)
```

\* declarações `theorem`/`lemma`, contando separadamente cada versão distinta de um mesmo arquivo.

## 1. Veredito

A proposta "RH e ¬RH existem e se complementam" tem uma forma lógica exata e consistente: **caso-a-caso**.
Se `A → X` e `¬A → X`, então `X`. Ler a proposta como "os dois lados valem ao mesmo tempo" é inconsistente
(`simultaneous_sides_impossible : ¬ (A ∧ ¬A)`).

A varredura procurou todo lugar em que essa forma aparece ou poderia aparecer: pares de teoremas com a mesma
conclusão e hipóteses complementares, dicotomias `A ∨ B` provadas com consumidores dos dois lados, e provas que
usam `by_cases`, `Classical.em`, `Or.elim` ou `WinWin`.

Resultado:

1. **O método já está aplicado** em todos os repositórios onde ele tem algo a fazer. Nenhum caso-a-caso novo
   fecha uma obrigação que já não esteja fechada.
2. **Ele fecha por completo um enunciado:** o Último Teorema de Fermat para primos regulares, com os casos I e II
   provados (`flt_regular`, M-Core `atk-kernel/ATK/FltRegular/FltRegular.lean`, trazido do projeto flt-regular segundo
   `ATK/FltRegular/ORIGEM.md`, arquivo idêntico em `e09b1952`). É o teorema de Kummer, de 1850. M-Core o usa em
   `FermatDezessete.lean`, `FermatDezenove.lean` e `BealFermatRegular.lean`.
3. **Ele produz teoremas válidos nos dois mundos** de Riemann (com e sem zeros fora da linha). Esses teoremas já
   estão no kernel em M-Core `atk-kernel/ATK/ZeroClasses/MundoFora.lean` (seção 4).
4. **Ele não fecha nenhum problema do milênio, nem Beal.** Em toda divisão encontrada, o ramo que falta é
   equivalente ao próprio problema. Isso está provado no kernel, de forma genérica e na instância P≠NP (seção 3).

## 2. Todas as divisões caso-a-caso encontradas

| Problema | Divisão | Ramo que existe | Ramo que falta | Prova de que o ramo que falta é o problema inteiro |
|---|---|---|---|---|
| P ≠ NP (descritores) | relógio total / não total; padrão constante / não | os dois ramos fáceis: `failure_of_not_total`, `failure_of_not_constant_correct` | total ∧ padrão constante (`FiniteDescriptorResidual`) | `residual_iff_universalFailure : FiniteDescriptorResidual ↔ UniversalFailure SATTarget` (branch `atk/p01-post-mincut-advance-20261001`) |
| P ≠ NP (P03) | `rangeFailureLaw_or_existsPerfectFlip : RangeFailureLaw ∨ ExistsPerfectFlip` | `RangeFailureLaw → ¬ InP SAT` | `ExistsPerfectFlip → ¬ InP SAT` | **novo neste branch:** `perfectFlip_missing_half_iff_target`. Todo decisor polinomial de SAT já é um "perfect flip" (`canonicalSAT_inP_implies_existsPerfectFlip`), então o mundo P = NP está dentro do ramo que falta |
| BSD | posto analítico 0, 1 / ≥ 2 | 0 e 1 como contrato externo (Gross–Zagier–Kolyvagin) | posto ≥ 2 | `bsd_realizable_low_plus_high_closes_universal` e `bsd_realizable_universal_implies_high` (m-core-bsd) |
| Hodge | codimensão p = 1 / p ≠ 1 | p = 1 a partir de Lefschetz (1,1), dado como entrada | p ≠ 1 | `concretePayload_iff_residual_given_codimOne` (m-core-hodge) |
| Beal | `c ≤ cota` / `c > cota` | as duas metades são entradas: verificação finita e redução via ABC | ABC efetivo com cota explícita, mais a verificação finita | `Beal_of_ABC_and_finite_check` (m-core-beal) só compõe as entradas |
| Navier–Stokes | explosão / sem explosão | sem explosão (Leray–Hopf) | explosão: `sorry` mais `CollapseAxioms` | `main_theorem` (millennium-navier-stokes-i) |
| Yang–Mills | `endpoint_envelope := Classical.em YangMillsExistenceMassGap` | — | os dois | o próprio arquivo diz: "excluded middle does not orient the scientific claim" |
| Riemann | RH / ¬RH, com alvo RH | RH → RH (trivial); ¬RH ⟺ existe zero fora da linha (`not_riemannHypothesis_iff_nonempty_offCriticalZero`, M-Core) | ¬RH → RH | `self_target_missing_half : (¬RH → RH) ↔ RH` (novo neste branch) |
| Riemann (colapso I) | ¬RH → I = 1; I ≠ 1 | — | o ramo ¬RH é **postulado**: o axioma `collapse_law_critical_line` diz que um zero fora força I = 1 | é exatamente "os zeros fora se auto-aniquilam", escrito como axioma. A auditoria do próprio repositório já o rotula como circular (`audit/language-corrected/atk__label-circular-rh-20261008`) |
| FLT, p < 300 | p ∤ xyz / p ∣ xyz | caso I, Sophie Germain–Legendre (`flt_caso_um_menor_300`) | caso II | `flt_iff_caso_dois` (M-Core) |
| **FLT, p regular** | p ∤ abc / p ∣ abc | **caso I e caso II** | **nada** | `flt_regular` (M-Core): **fechado** |

Nenhuma dicotomia provada tem consumidores nos dois lados com a mesma conclusão, exceto
`ramos` (M-Core `ZeroClasses/Hipotetico.lean`). Lá os dois ramos (parte real racional ou irracional) concluem
`¬RiemannHypothesis` sob a hipótese `HFora`, o que é imediato.

## 3. Por que nunca fecha o próprio problema (verificado no kernel)

```lean
theorem missing_half_iff_target {Opp Branch Target : Prop}
    (hOpp : Opp → Branch) (hTarget : Target ↔ ¬ Opp) :
    (Branch → Target) ↔ Target
```

Se o mundo contrário `Opp` cai dentro do ramo complementar, então a metade que falta equivale ao alvo. Esse é o
padrão de todas as linhas da tabela. Um decisor de SAT em tempo polinomial é total e de padrão constante correto,
e também é um "perfect flip". Uma curva com posto ≥ 2 é um contraexemplo possível a BSD. Uma classe de Hodge com
p ≥ 2 é um contraexemplo possível a Hodge. Um zero fora da linha é exatamente ¬RH.

Instâncias neste branch (o status de verificação está na seção 6):

```lean
theorem perfectFlip_missing_half_iff_target :
    (ExistsPerfectFlip → SATNotInP) ↔ SATNotInP
theorem winwin_over_p03_iff_target :
    ((RangeFailureLaw → SATNotInP) ∧ (ExistsPerfectFlip → SATNotInP)) ↔ SATNotInP
theorem self_target_missing_half {RH : Prop} : (¬ RH → RH) ↔ RH
```

`missing_half_iff_target` é construtivo. A dependência de axiomas de cada teorema está na seção 6.

## 4. Onde a proposta produz teoremas de verdade: válidos nos dois mundos

O lugar certo da ideia é um `X` **diferente** do alvo, verdadeiro com ou sem RH. M-Core já tem isso em `main`
(arquivos byte-idênticos no commit `e09b1952`, cuja execução `ATK kernel check` 40120636882 anota
`ATK-KERNEL CERTIFIED 6909/6909`):

| Ideia do usuário | Teorema | Arquivo (M-Core `atk-kernel/ATK/`) | Status |
|---|---|---|---|
| "a linha não cai" | `linha_sobrevive`: a linha crítica tem zeros em qualquer mundo | `ZeroClasses/MundoFora.lean` | incondicional |
| "as duas coexistem" | `coexistencia`: sob `HFora`, a linha e os zeros fora estão ambos ocupados | idem | condicional a `HFora` (= ¬RH) |
| "um espelha o outro" | `linha_espelho`, `ponto_medio`, `fora_fixa_eixo`: a linha é o conjunto fixo de `s ↦ 1 − s̄`, e os zeros fora, se existirem, determinam `Re s = 1/2` | idem | incondicional |
| "se compensam" | `equilibrio`: `Σ (β − 1/2) = 0` sobre os zeros fora até cada altura; `centro_fora` | idem | incondicional |
| "são muito pequenos" | `esparsidade` (Bohr–Landau): no máximo `C·T` zeros a distância > δ da linha até a altura `T` | idem | incondicional |
| "quase todos na linha" | `quase_todos_perto` | idem | condicional a `CrescimentoN` (B10) |
| "muito grandes, tendendo ao infinito" | `dicotomia_mundo`: os zeros fora são finitos ou aparecem em alturas arbitrariamente grandes; `rh_acima`: se forem finitos, acima de uma altura todos estão na linha | idem | incondicional |
| "depois do infinito estabiliza" | `oscilacao_01`, `oscilacao_sinal`: nos hiper-reais uma oscilação 0/1 vale exatamente 0 ou 1 | `OscilacaoHiperreal.lean` | incondicional; qual dos dois valores sai depende do ultrafiltro, de modo não construtivo |
| "tolerância e margem de erro" | `estado_DN_dicotomia`: a distância de Báez-Duarte `D_N` tende a 0 ou a um limite finito positivo; escolher entre os dois **é** RH | `RiemannStates.lean` | incondicional; a escolha está aberta |
| "um parâmetro" | `li_criterion_finite`, `li_criterion_finite_symm` (coeficientes de Li, modelo finito) | m-core-riemann `atk/riemann-li-criterion-finite-20261011` | execução 38154663458, sucesso |

Esses teoremas mostram até onde a ideia vai. Ela descreve com exatidão como os dois mundos teriam de ser. Ela não
escolhe entre eles.

## 5. O que fecharia algo novo com a proposta

São alvos `X ≠ RH` com as duas metades demonstráveis. Nenhum deles está formalizado em nenhum dos 28 repositórios:

- **Littlewood (1914):** `π(x) − li(x)` muda de sinal infinitas vezes. A prova original é exatamente caso-a-caso:
  ramo RH pela fórmula explícita, ramo ¬RH pelo zero fora de maior parte real. Exige a fórmula explícita de
  von Mangoldt, que não está em Mathlib v4.19.0.
- **Deuring–Heilbronn (1933–34):** `h(−d) → ∞`. Ramo GRH por Hecke, ramo ¬GRH por Deuring e Heilbronn.
- **P vs NP: busca universal de Levin.** É um algoritmo explícito que encontra atribuições para fórmulas
  satisfatíveis e é ótimo, até um fator constante, em qualquer mundo. Em particular, ele roda em tempo polinomial
  nessas instâncias se e somente se P = NP. É um teorema dos dois mundos, formalizável no modelo de máquina do
  repositório.

O modelo finito de Li não serve como exemplo. Com finitos zeros, a oscilação de `Σ Re(w_i^n)` sai de um argumento
único, sem divisão em casos. A divisão só passa a ser necessária com infinitos zeros, como em Littlewood.

## 6. Evidência

| Item | Valor |
|---|---|
| Branch | `atk/winwin-missing-half-audit-20261024` (repositório `ShantiDraconis/m-core-p-vs-np`) |
| Pai | `19d2fb6bca6264ed3f8195810ef87f1d6ff2281d` (`atk/p02-material-inhabitant-20261007`; mesmo `PNPNTMTableauEncoding` de `6c467fbb`, verificado na execução 37914345859, e `PNPNTMTableauClosure` com a correção `2103b5d6`) |
| Arquivos novos | `lean/MCore/Integration/WinWinLogic20261024.lean` (só o núcleo do Lean), `lean/MCore/Integration/WinWinMissingHalfAudit20261024.lean` (importa `MCore.Real.P03PerfectFlipDichotomy`) |
| Mathlib | `c44e0c8ee63ca166450922a373c7409c5d26b00b` (`lake-manifest.json` copiado de `685593f0`) |
| Arquivos pré-existentes alterados | nenhum arquivo-fonte; só `lake-manifest.json` (fixação do Mathlib) |
| Verificação local | `WinWinLogic20261024.lean` com Lean 4.19.0: `missing_half_iff_target` e `simultaneous_sides_impossible` sem axiomas; `winwin_close` e `self_target_missing_half` com `[propext, Classical.choice, Quot.sound]` |
| Execução CI | RUN_PLACEHOLDER |
| Varredura | `WINWIN_SCAN_SUMMARY.json`, `tools/winwin_scan.py`, `tools/extract.sh` |

### Achado colateral: a dicotomia P03 nunca foi verificada pelo kernel

O fecho de importações de `MCore.Real.P03PerfectFlipDichotomy` tem 187 módulos e inclui
`MCore.Real.PNPNTMTableauClosure`, pelo caminho
`P03RangeFailureFrontier → P02InvariantCore → P02BehavioralAlignment → P02ExactDiagonalFrontier →
P02ComplementRunRealization → PNPNTMTableauClosure`. O arquivo está, idêntico (blob `80d0362c`), em 8 branches.
Em nenhum deles uma execução de CI compilou esse fecho:

- `6c467fbb`: a execução 40137017331 (commit `c866851d`, primeira tentativa deste branch) falha em
  `PNPNTMTableauClosure.lean` com `universe level metavariables` e `unknown constant …NTMTableauSizeCertificate.mk._flat_ctor`;
- `5572a4c9`, `9966966b`, `28c64098`: o `lakefile` não exige Mathlib, mas `PNPNTMTableauEncoding` usa táticas do
  Mathlib. A compilação local com Lean 4.19.0 falha ali;
- `1779db20`, `08a17e64`, `685593f0`: o núcleo tableau falha (execução 37914345859);
- `19d2fb6b`: veja a execução acima.

Logo `rangeFailureLaw_or_existsPerfectFlip` e `canonicalSAT_inP_implies_existsPerfectFlip` só contam como
verificados se o job `p03-instance` passar. A conclusão da seção 3 não depende disso. O lema genérico
`missing_half_iff_target` só precisa da implicação "P = NP ⇒ existe perfect flip", que tem uma prova curta e
direta no próprio arquivo P03.

Limites da varredura: a comparação é sintática, sobre conclusões normalizadas como texto. Hipóteses implícitas e
divisões feitas em modo termo não aparecem. Só as pontas dos branches foram lidas (clones rasos).
