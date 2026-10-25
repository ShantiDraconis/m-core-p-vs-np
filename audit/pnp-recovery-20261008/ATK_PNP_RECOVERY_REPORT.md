# ATK — Recuperação e integração P ≠ NP — 2026-10-08

```
ATK-PNP: OPEN_MATH (1 obrigação) | integração atk/pnp-recovery-integration-20261008
         | pai FROZEN 0dd09383932446ba67e673f69cd8740f85a80b87
         | CI P01: run 36897479263 (15b6c36043721e827930c98babbaa3e0e9f50456)
         | RECUPERADO: P01ConstructionGap (SAT ∈ NP)
         | LACUNA REAL: G21Pointwise ≡ ¬ InP SAT
         | PRÓXIMO PRODUTOR: nenhum candidato existente; exige resultado matemático novo
```

## 1. Veredito

A prova terminal de P ≠ NP **não está completa** e **não existe dispersa** nos repositórios examinados.

- **P01 — SAT ∈ NP: FECHADO.** Já existia, demonstrado e verificado pelo kernel, em `MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed`. Ele foi recuperado e integrado sem alterar nenhum arquivo existente.
- **G21Pointwise: OPEN_MATH.** É, por definição, `UniversalFailure SATTarget`. Equivale, provadamente no kernel, a `¬ InP SATTarget`, ou seja, "SAT não está em P". Combinado com P01, implica `PneqNP`. Nenhum habitante foi encontrado. Como SAT ∉ P equivale a P ≠ NP (pelo teorema de Cook–Levin), essa obrigação é o próprio problema do milênio. Não é uma lacuna de integração.

O teorema integrado tem exatamente uma hipótese:

```lean
theorem pneqnp_of_g21 (hG21 : G21Pointwise) : PneqNP
-- axiomas: [propext, Classical.choice, Quot.sound]
```

O critério `theorem final_proof : PneqNP := by exact recovered_material_proof` **não é satisfeito**, porque não existe `recovered_material_proof` para G21.

## 2. Enunciado terminal e fidelidade

| Objeto | Definição Lean | Arquivo |
|---|---|---|
| `PneqNP` | `¬ ∀ L : BitLanguage, InP L ↔ InNP L` | `lean/MCore/Real/CanonicalFinalProof.lean` |
| `InP` / `InNP` | `Nonempty (PolyDTMRealization L)` / `Nonempty (PolyNTMRealization L)` | idem |
| Modelo | TM/NTM de uma fita, estados `Fin (k+1)`, alfabeto `Option Bool`, transições locais | `lean/MCore/Real/Model.lean` |
| Tempo polinomial | `T n ≤ c · (n+1)^e` | `CanonicalFinalProof.lean` |
| SAT | `IsCNF φ ∧ ∃ σ, evalCircuit σ φ = true`, codificado por `circuitBitEncoding` (com `decode_encode` provado) | `SATMachine.lean`, `CanonicalSATBoundary.lean`, `CanonicalCircuitBits.lean` |

Diferenças em relação ao enunciado clássico, confirmadas pelo auditor independente:

- uma única fita;
- alfabeto {branco, 0, 1};
- forma específica do limite polinomial;
- variáveis codificadas em unário.

Sabe-se que P e NP não mudam com essas escolhas, mas a equivalência com um modelo padrão (por exemplo, `Turing.TM2ComputableInPolyTime` do Mathlib) **não está formalizada**: `ExternalModelMatch` só existe na forma interna trivial. Esta é uma `SEMANTIC_GAP` demonstrável em princípio e independente de G21. O modelo antigo, que tinha um campo de codificador arbitrário, foi refutado pelo próprio projeto (`FinalProofAttack.current_SATNotInP_refuted`) e não é usado aqui.

`inP_subset_inNP` está provado (`CanonicalPSubsetNP`). Portanto, `PneqNP` equivale a "existe uma linguagem em NP fora de P".

## 3. Tabela de proveniência — cadeia terminal integrada

| Papel | Nome Lean | Arquivo | Commit / ref | Estado |
|---|---|---|---|---|
| Endpoint | `CanonicalFinalProof.PneqNP` | `CanonicalFinalProof.lean` | `0dd09383…` | definição |
| Lema de fechamento | `target_failure_implies_p_ne_np` | `CanonicalFinalProof.lean` | `0dd09383…` | kernel ✔, sem axiomas |
| Equivalência | `universal_failure_iff_not_in_p` | `CanonicalFinalProof.lean` | `0dd09383…` | kernel ✔ (clássico) |
| Equivalência | `failure_generator_iff_universal_failure` | `FailProofAllGaps.lean` | `0dd09383…` | kernel ✔ |
| Ponte P01 → InNP | `P01FinalCertificate.construction_closes_p01` | `P01FinalCertificate.lean` | `0dd09383…` | kernel ✔ |
| **Habitante P01** | `P01RawTotalizationProducer.p01ConstructionGap_closed` | `P01RawTotalizationProducer.lean` | `0dd09383…` (FROZEN); CI run `36897479263` em `15b6c360…` (arquivo e imports idênticos byte a byte) | **kernel ✔**, `[propext, Classical.choice, Quot.sound]` |
| Composição | `sat_in_np_recovered`, `pneqnp_of_g21`, `integration_status` | `lean/MCore/Integration/PNPRecoveredFrontier20261008.lean` | esta branch | kernel ✔ |
| **Hipótese restante** | `G21Pointwise` | idem (corpo idêntico a `P02G21G22Attack.G21Pointwise`) | — | **sem habitante (OPEN_MATH)** |

## 4. Classificação das lacunas (Fase 3)

| Obrigação / branch | Classe | Evidência |
|---|---|---|
| `P01ConstructionGap` nas 3 branches prioritárias | `DEPENDENCY_GAP` → **resolvida** | habitante válido encontrado em `0dd0938` |
| `atk/p01-raw-closure-unified-20261001` (`fc21c82a…`) | `KERNEL_FAILURE` | `P01RawSourceSplit.lean:21` (tipo incompatível, `sorryAx`); `P01CheckedVerifierFiniteState.lean` usa `Fintype` (Mathlib, que não é dependência); `P01ExactBoundedCircuitProducer.lean` com cerca de 15 erros. CI RED: runs `36791113731`, `36791113653` |
| `atk/direct-p01-inhabitant-close-20260930` (`9f108133…`) | `KERNEL_FAILURE` | `P01CheckedEvalRunBoundedHelpers.lean:126` (metas não resolvidas); seu P01 continua condicional a `P01VerifierPhase`. CI RED: run `36713740303` |
| `atk/p01-preserving-terminal-materialize-20261005` (`fb7ddf8f…`) | parcial ✔ | `preservingUnaryReaderGap_material` compila (`[propext, Quot.sound]`); `ReaderBeforeP01Construction` é apenas uma `def Prop`, não um teorema. O alvo `MCore` não importa esses arquivos. CI: run `37349036116` OK, `37349036128` RED |
| `G21Pointwise` | `MATERIAL_GAP` (OPEN_MATH) | §6 e `ATK_NEGATIVE_SEARCH_CERTIFICATE.json` |
| Modelo interno ↔ modelo padrão | `SEMANTIC_GAP` | `ExternalModelMatch` só na forma interna |
| Cook–Levin no modelo interno | `SEMANTIC_GAP` (não bloqueia G21 → PneqNP) | não formalizado |
| Circularidade | nenhuma | §5 |
| Axiomas extras | nenhum na cadeia | §5 |

Outros produtores de P01 declarados:

- `atk/p02-material-inhabitant-20261007` e `atk/p01-raw-closure-final-20261001`: **não verificados no kernel neste ciclo**. Os dois `lakefile.toml` exigem `mathlib` `v4.19.0`, mas o `lake-manifest.json` não fixa o pacote, de modo que o build não é reproduzível como está. São redundantes, já que P01 está fechado sem Mathlib.
- `atk/p01-final-plus-preserving-reader-20261005` (= `0dd0938`): **compila** e é o usado.

## 5. Auditoria de axiomas e de separação

`#print axioms`, executado localmente com Lean 4.19.0 e reproduzido no workflow desta branch:

- `p01ConstructionGap_closed`, `sat_in_np_recovered`, `pneqnp_of_g21`, `g21_iff_sat_not_in_p` e `integration_status` → `[propext, Classical.choice, Quot.sound]`
- `g21_iff_universal_failure` → `[propext, Quot.sound]`

Auditoria de separação (`PNPCircularityAudit20261008.lean`): busca em largura sobre o fecho transitivo, cobrindo tipos, corpos, construtores e recursores.

- Fecho de `p01ConstructionGap_closed`: **4.452 constantes**, nenhuma do lado do limite inferior. A lista proibida cobre `PneqNP`, `InP`, `UniversalFailure`, `FailureGenerator`, `G21Pointwise`, `PolyDTMCandidate`, `PolyDTMCandidate.CorrectAt`, `sorryAx` e outros.
- O controle positivo exige detecção em profundidade ≥ 3 (`PolyDTMRealization`, a partir de `pneqnp_of_g21`) e exercita o ramo de falha.
- Observação do auditor, aceita: a correção do P01 já decorre do kernel junto com os axiomas padrão. Esta auditoria verifica uma coisa mais estreita: que o lado SAT ∈ NP sequer menciona o lado do limite inferior.

## 6. Busca de habitantes e certificado negativo

Escopo detalhado, com todas as refs e SHAs completos, em `ATK_NEGATIVE_SEARCH_CERTIFICATE.json`. Em resumo:

- **m-core-p-vs-np:** 684 branches com histórico completo (5.330 commits), 53 refs de PR, sem tags. 1.385 blobs Lean nas pontas, 1.974 só no histórico.
- **Outros repositórios** (pontas de todas as branches): M-Core (183 refs), millennium-p-vs-np-I (14), axiomatic-millenium (48), proofs-multiprover (2) e universal-proof-hub (9).
- **Métodos:**
  - varredura por tipo de declaração;
  - varredura com resolução transitiva de aliases (pega nomes diferentes com o mesmo corpo);
  - cruzamento com as 105 hipóteses distintas de todo teorema que conclui `PneqNP`;
  - varredura `isDefEq` no kernel, feita pelo auditor independente em 4 branches P02 recentes e nesta branch.
- **Resultado:** todo teorema que conclui `PneqNP` recebe uma hipótese, e nenhuma dessas hipóteses tem habitante incondicional. Os 9 candidatos aparentes foram examinados e rejeitados. Cada um é `sorry`, axioma de falsificação, sonda com metas abertas ou condicional via `variable` (lista no JSON).

`ATK_SEMANTIC_PROOF_MAP.json` registra 67 equivalências do repositório entre G21 e outros nomes (`P02Target`, `UniversalSATLowerBound`, `FINAL_OPEN_MATH`, `NormalizedAdversary`, `TotalSemanticFailureProducer`, …). Todas reformulam a mesma obrigação. Nenhuma a reduz a algo já provado.

## 7. Verificação independente

Um segundo processo, sem acesso às classificações do primeiro além das afirmações a verificar, refez a auditoria. Resultado: afirmações 1–5 e 7 **confirmadas**; afirmações 6 e 8 **parciais**. As correções foram aplicadas nesta branch:

1. O run `37354059689` (em `0dd0938`) **não** compila o produtor P01. A evidência de CI do produtor é o run `36897479263` em `15b6c360` (ancestral, com o produtor e seus imports idênticos byte a byte), que executa `lake build MCore.Real.P01RawTotalizationProducer`. Isso foi verificado diretamente. O workflow novo desta branch também compila o produtor.
2. O controle positivo da auditoria de separação era raso e não exercitava o ramo de falha. Foi substituído por um controle com busca em largura, profundidade ≥ 3 e teste do ramo de falha.
3. A lista proibida não cobria `PolyDTMCandidate` nem `CorrectAt`. Agora cobre, por nome completo.
4. Formulações corrigidas: G21 é *definicionalmente* `UniversalFailure SATTarget`, e *classicamente equivalente* a `¬ InP SATTarget`. A expressão "ou algo mais forte", que não havia sido verificada, foi removida.
5. O auditor reproduziu o fecho de 4.452 constantes (o mesmo número), refez o kernel sobre ele num ambiente vazio ("REPLAY OK") e compilou do zero um `git archive` da integração, com 154 módulos.

## 8. Fase 5 — o que falta construir

O produtor que falta é um termo de tipo

```lean
∀ candidate : PolyDTMCandidate, ∃ x : BitString,
  ¬ candidate.CorrectAt (SATBits circuitBitEncoding) x
```

Isso é um limite inferior superpolinomial para SAT contra **toda** máquina determinística polinomial. Não existe na literatura, e nenhum fragmento examinado se aproxima dele. As barreiras conhecidas se aplicam a qualquer tentativa:

- **Relativização** (Baker–Gill–Solovay): diagonalização e simulação pura não bastam.
- **Provas naturais** (Razborov–Rudich): argumentos combinatórios "construtivos e amplos" não bastam, sob hipóteses criptográficas padrão.
- **Algebrização** (Aaronson–Wigderson).

O próprio projeto já registra em `Barrier/Audit.lean` que as construções atuais aparentam relativizar. As rotas falsificadas e congeladas (ponto fixo literal, `SameInputCore`, `UniformCompilerValueComputable` e outras) confirmam esse diagnóstico. **Não produzi uma demonstração de G21 e não há base para afirmar que uma esteja próxima.** Uma tentativa honesta exigiria ideias matemáticas novas, capazes de contornar as três barreiras. Não há uma composição de fragmentos disponível.

Trabalho real e demonstrável que ainda é possível, independente de G21:

- **SEMANTIC_GAP 1:** provar `ExternalModelMatch` entre o modelo interno e `Turing.TM2ComputableInPolyTime`, que exige Mathlib.
- **SEMANTIC_GAP 2:** formalizar Cook–Levin no modelo interno, o que tornaria `PneqNP ↔ G21Pointwise` um teorema.

## 9. Resultados aptos a publicação (Fase 8)

| Resultado | Natureza | Apto a DOI? |
|---|---|---|
| `p01ConstructionGap_closed` | Formalização em nível de máquina de Turing de um resultado clássico (SAT ∈ NP; ver Cook 1971) | Sim, **como artefato de formalização**. Comparar com mecanizações existentes de Cook–Levin, por exemplo Gäher & Kunze (Coq, ITP 2021) e Balbach (Isabelle AFP, 2023), antes de afirmar originalidade |
| `pneqnp_of_g21` / `integration_status` | Redução condicional, já conhecida informalmente | Só como parte do artefato acima; **não** é resultado sobre P vs NP |
| Qualquer afirmação de P ≠ NP | — | **Não.** Não há prova terminal |

Sucesso de CI ou atribuição de DOI não equivalem a aceitação científica. Uma revisão por especialistas em formalização é recomendada para o artefato P01.

## 10. Reprodução

```bash
git checkout atk/pnp-recovery-integration-20261008
# Lean 4.19.0 (lean-toolchain), sem dependências externas
lake build MCore.Real.P01RawTotalizationProducer
lake build MCore.Integration.PNPRecoveredFrontier20261008 MCore.Integration.PNPCircularityAudit20261008
# esperar: SEPARATION_AUDIT CONTROL PASS / PASS ×2 e axiomas apenas propext, Classical.choice, Quot.sound
python3 -I audit/pnp-recovery-20261008/tools/scan2.py BLOBDIR BLOBMAP OUT.json   # ver tools/extract.sh
```

Workflow: `.github/workflows/atk-pnp-recovery-integration.yml`.

## 11. Certificação CI desta integração

| Commit | Run | Workflow | Resultado |
|---|---|---|---|
| `4b799f27be0b60c4f32fc0fd2938213d6576dfca` | `37822209048` | `atk-pnp-recovery-integration.yml` | success. Passos: build do produtor P01, build da integração e da auditoria de separação, auditoria exata de assinatura e axiomas |
| `4b799f27be0b60c4f32fc0fd2938213d6576dfca` | `37822209033` | `certificate.yml` | success |
| `4b799f27be0b60c4f32fc0fd2938213d6576dfca` | `37822209113` | `fail-proof-all-gaps.yml` | success |

O que esta certificação cobre: P01 (SAT ∈ NP) fechado e a redução condicional `G21Pointwise → PneqNP`. Ela **não** certifica P ≠ NP.

## 12. Auditoria do "centro" (START–CENTER–FINISH e indeterminação)

Pergunta testada: a camada `FinalFail` do M-Core (`ClosedCenterHard`, `FundamentalIndeterminacy`, `RelationalHardAtom`, `CoreIndeterminacyTests`, `MinimalOpenBridge`), em `ShantiDraconis/M-Core@53d58bceed3424a435eb54e01cd6d3f17324a630`, contém uma prova transportável para `G21Pointwise`, ou uma incompatibilidade lógica demonstrável no centro?

As definições foram portadas literalmente para `lean/MCore/Integration/PNPCenterTransportAudit20261008.lean`, com a proveniência anotada, e todos os resultados abaixo foram verificados no kernel:

| # | Teorema | Resultado | Axiomas |
|---|---|---|---|
| 1 | `#center_layer_model_free` | As 8 declarações portadas não alcançam nenhuma constante do modelo de máquinas (`PolyDTMCandidate`, `TM`, `SATBits`, `InP`, `PneqNP`, `G21Pointwise`). O controle positivo (`pnpCenter`) é sinalizado corretamente. | — |
| 2 | `closedCenterHard_for_g21`, `closedCenterHard_for_not_g21` | `ClosedCenterHard` é habitado tanto para G21 quanto para ¬G21: a estrutura não distingue as respostas | nenhum |
| 3 | `terminalChain_exists_iff` | Uma cadeia terminal para `F` existe **se e somente se** `F` está provado: a cadeia não acrescenta conteúdo | nenhum |
| 3b | `closedCenter_eq_to_neq_impossible` | A instância proposta `ClosedCenterHard (P = NP) Center (P ≠ NP)` é **contraditória** para todo centro, porque força `¬PneqNP ↔ PneqNP` | nenhum |
| 4 | `firewall_closed_by_true_fields` | `FirewallClosed` é satisfeito com todos os campos `True`; não inspeciona código | nenhum |
| 5 | `pnpCenter_determined`, `pnpCenter_not_indeterminate` | O centro real de P vs NP é **determinado** (terceiro excluído). A "indeterminação" só existe em modelos de brinquedo (`twoBranchResolution` usa `Bool` com tudo admissível). A determinação não revela qual ramo vale | clássicos |
| 6 | `exists_forall_failure_false` | `∃ x, ∀ M, M falha em x` é **falso** para SAT: uma máquina de um estado acerta qualquer entrada fixa. Só a forma `∀ M, ∃ x` (G21) é um alvo com sentido | clássicos |

Conclusão: não existe, e não pode existir, transporte dessa camada para G21. Os teoremas dela são genéricos em `Prop`/`Type`, então só produzem G21 quando instanciados com setas que já contêm a prova (resultado 3). A camada é coerente como cálculo abstrato, mas não guarda conteúdo de complexidade. A proposição que falta continua sendo exatamente `G21Pointwise`. `AcceptedInhabitants` recebe o conteúdo como argumento (por exemplo, `producePvsNPAccepted`, `produceRiemannAccepted (h : ¬ RiemannHypothesis)`); não constrói habitante.

Observação de nomenclatura: `RelationalHardAtom.FailAt` significa "duas ramificações distintas", não "a máquina falha". A coincidência com `UniversalFailure` não indica nenhuma relação entre os dois.

## 13. Conferência dos certificados existentes (2026-10-09)

Unidade de auditoria: declaração Lean + arquivo + SHA + run com sucesso + `#print axioms`. O resultado completo, registro a registro, está em `PNP_MATERIAL_PROOF_MANIFEST.json`.

Fontes lidas:
- `m-core-p-vs-np@9efeb9b7…` (`CERTIFICATES/`, `certificates/`, `GATE_LEDGER.json`, `audit/ATK_P01_MATERIAL_FRONTIER_V1.json`)
- `M-Core@01d8d766…` (`certs/`, `evidence/`, `final-proof/`)

| Verificação | Resultado |
|---|---|
| Runs citados | 46: **44 existem, terminaram com sucesso e têm head no SHA citado**; 2 não existem em nenhum dos dois repositórios (`35378862267` em `M-Core certs/final_external/v1/manifest.json`, `35565114760` em `M-Core final-proof/global_sources.json`) |
| SHAs do `m-core-p-vs-np` recompilados aqui (Lean 4.19.0) | **26 de 26** sem Mathlib compilam. Todos os teoremas citados e todos os nomes que o workflow certificador audita usam apenas `propext`, `Classical.choice` e `Quot.sound`; nenhum `sorryAx` |
| SHAs com Mathlib | `dfb3e60d` (parser) e `9ebd51f5` (witness guess): o run citado compila o módulo declarante, mas sem passo explícito de auditoria de axiomas. Não foram recompilados aqui |
| CI cobre o módulo do teorema? | **2 divergências**: `GATE_LEDGER` atribui `tmAsNTM_*`/`tmHaltsWithin_iff_ntmHaltsWithin` (`833fe0de`) e `consumeOneTape_correct`/`consumeThreeTape_correct` (`4eb4051f`) a runs genéricos (`certificate`, `fail-proof-all-gaps`) que **não compilam** `P01DeterministicNTMEmbedding` nem `P01EvalCursorConsume`. Os sete teoremas passam no kernel local, com axiomas padrão; só a evidência de CI citada está errada |
| Os oito certificados P01 | Todos `KERNEL_VERIFIED_LOCAL_AND_CI` (ou CI apenas, no caso do parser com Mathlib). Cada um certifica **um componente** e declara no próprio texto que não habita `P01MachineConstruction` |
| `ATK_TERMINAL_P_VS_NP_e927d326.json` | Runs e build conferem. O próprio certificado diz que **não** certifica SAT ∉ P nem P ≠ NP |
| `ATK_ACCEPTED_SEMANTIC_7OF7` (M-Core) | Runs conferem. É um "universo condicional": os habitantes vêm de hipóteses aceitas |
| Certificados terminais de P ≠ NP | **0** |

Correção de estado: os índices em `main` (`GATE_LEDGER.json` e `ATK_P01_MATERIAL_FRONTIER_V1.json`, atualizado hoje em `9efeb9b7`) ainda registram P01 como `OPEN_MATH`. Isso está desatualizado: `p01ConstructionGap_closed` está FROZEN em `0dd0938` e verificado (seções 3 e 11). Os arquivos em `main` e no M-Core não foram alterados por esta auditoria.

## 14. Tableau de Cook–Levin (versões com Mathlib)

CI: branch `atk/pnp-tableau-mathlib-ci-20261009`, run `37914345859`. As quatro versões foram compiladas nos SHAs de origem, contra o mesmo Mathlib fixado (`c44e0c8e`, manifest de `685593f0`).

| SHA (branch) | Resultado |
|---|---|
| `6c467fbba91503d25e91d2bab8b804aebf34dc9f` (`atk/p02-lane4-reuse-t10-audit-20261003`; o mesmo arquivo está em `atk/p02-material-inhabitant-20261007`) | **KERNEL_VERIFIED_CI**. `tableau_correctness_iff`, `tableau_soundness_from_satLanguage`, `tableau_completeness_to_satLanguage`, `boundedExec_weight_poly` e `boundedExec_encoded_length_poly`: `[propext, Classical.choice, Quot.sound]` |
| `1779db20…` (`p02-e1-c1-left-validate`) | KERNEL_FAILURE (linha 6310: `rewrite` falhou; 6001: metas não resolvidas) |
| `08a17e64…` (`p02-e1-c2-right`) | KERNEL_FAILURE (linha 6464: construtor anônimo inválido; 6313: metas não resolvidas) |
| `685593f0…` (`p02-lane4-terminal-densify`) | KERNEL_FAILURE (linha 2621: timeout de heartbeats; 2699–2707: identificadores `ntmInitial_*_exists_unique` inexistentes) |

O que está provado em `6c467fbb`:
```lean
tableau_correctness_iff : ∀ (M : PolyNTMCandidate) (x : BitString) (t : ℕ),
  SATLanguage (boundedExecCircuit_NTM M x t) ↔ M.machine.AcceptsWithin t (initialNTMConfig M.machine x)
boundedExec_encoded_length_poly : ∀ M x t,
  (encodeCircuit (boundedExecCircuit_NTM M x t)).length ≤ tableauEncodingCoeff M * (x.length + t + 1)^4
```
Esse é o núcleo semântico do Cook–Levin: a fórmula é satisfatível exatamente quando a máquina aceita, e seu tamanho é polinomial. Para obter `PneqNP → G21Pointwise` ainda faltam:
1. uma máquina determinística polinomial, no modelo do repositório, que **calcule** `x ↦ encodeCircuit (boundedExecCircuit_NTM M x (T |x|))`;
2. a composição dessa máquina com um decisor hipotético de SAT (`PolyDTMCandidate`), dando um decisor para qualquer linguagem NP;
3. o teorema resultante.

O módulo não está ligado à branch de integração, porque depende de Mathlib e a integração não depende. Isso fica para quando os passos 1 e 2 existirem.

## 15. Pendências deste ciclo

- **Matriz das 32 obrigações:** a lista não foi encontrada nesta conversa nem nos repositórios examinados (busca em `.md`, `.json` e `.yaml` de todas as branches). É preciso indicar o arquivo ou a fonte.
- Repositórios de Riemann, Beal, BSD, Hodge, Yang–Mills, Navier–Stokes e Poincaré: ainda não examinados.
- Entregáveis da Fase 9: este relatório consolida o grafo de dependências, o min-cut, os produtores recuperados, a auditoria de axiomas e circularidade, os resultados do kernel e o pacote de revisão. Os dois JSON cobrem o índice de evidências e o mapa semântico desta lane.

## 16. Atualização da fronteira — 2026-10-25

```
ATK-PNP: OPEN_MATH (1 obrigação) | ledger GATE_LEDGER_V3_20261025.json (substitui main:GATE_LEDGER.json V2)
         | P01: CLOSED  (o V2 de main ainda diz current_gate P01, hard 2)
         | G21: OPEN_MATH, current_gate, hard 1
         | verificado neste ciclo: P02ComplementRunRealization (reparado) e P02ExactDiagonalFrontier, run 40147407179
         | rotas fechadas: P03 RangeFailureLaw, win-win sobre P03, modelo de encode arbitrário
```

### 16.1 Estado atualizado

| Portão | Estado | Evidência |
|---|---|---|
| P01 — SAT ∈ NP no modelo endurecido | **CLOSED** | `p01ConstructionGap_closed` @ `0dd09383`; runs 36897479263, 37913791428, 37822209048, 38420031935 (PR #44); axiomas padrão |
| G21 — `UniversalFailure SATTarget` | **OPEN_MATH** | nenhum habitante; `g21_iff_sat_not_in_p` e `pneqnp_of_g21` (run 37848515115); nova equivalência `total_exact_diagonal_iff_universal_failure` (run 40147407179) |

O `GATE_LEDGER.json` de `main` (blob `dce43595`, esquema V2) está desatualizado desde 09/10: ainda aponta P01
como portão atual e duas obrigações duras. O arquivo `GATE_LEDGER_V3_20261025.json` desta pasta é a versão
corrigida e pode substituí-lo diretamente. Ele mantém o histórico do P01 marcado como `CLOSED_HISTORICAL`.

### 16.2 Busca refeita

Desde o certificado negativo de 09/10, 8 branches foram atualizadas e apareceram 22 blobs `.lean` novos. Nenhum
deles habita G21, `UniversalFailure` ou `PneqNP`. Dois casos parecem habitantes e não são:

- `PNPMaterialAtoms.lean`, cópia de auditoria em `atk/language-audit-20261015`:
  `example : FailureGenerator (SATBits circuitBitEncoding) := by constructor`. O `constructor` deixa abertos os dois
  campos, `counterexample` e `fails`. O arquivo está fora do build do Lean.
- `current_SATNotInP_refuted`, em `audit/ATK_UNIFIED_SOURCE_BATCH04_20261009.lean` (`main`): refuta `SATNotInP` só no
  modelo antigo `FinalProofAttack`, que tem um codificador de entrada arbitrário. Nesse modelo toda linguagem
  está em P. O modelo endurecido não tem esse campo.

O PR #44, aberto e ainda não integrado, recompõe o mesmo corte por outro caminho: `PNPAfterP01.pneqnp_of_universal_failure`.

### 16.3 Avanço verificado

Branch `atk/p03-closure-repair-20261025`, run 40147407179, job `certify` 121031595224, sucesso:

- `P02ComplementRunRealization` foi reparado com 2 correções em corpos de prova, sem alterar nenhum enunciado.
  Agora compila. `complement_reduce_correct : CanonicalSAT (R_M x) ↔ ¬ DeclaredAccepts M x` vale para todo
  candidato total `M`. É a correção do tableau de Cook–Levin aplicada ao complemento do próprio candidato.
- `P02ExactDiagonalFrontier` compila pela primeira vez. `total_exact_diagonal_iff_universal_failure` dá mais uma
  forma exata de G21.

Axiomas: `runBranches_complement_to_tm_run` e `complement_correctAt` usam só `[propext]`; os demais usam
`[propext, Classical.choice, Quot.sound]`.

### 16.4 Rotas fechadas (não reabrir)

1. **P03 `RangeFailureLaw`: esperada falsa** (esboço; não verificado pelo kernel). A lei exige que todo candidato
   total `M` erre SAT em algum ponto da imagem do seu próprio `R_M`. Um candidato com acesso ao próprio código,
   pelo teorema de recursão, faz o seguinte com uma entrada `y`: lê `x` nas cláusulas de configuração inicial,
   recalcula `R_M x` e compara com `y`, simula a si mesmo em `x` (que é menor) e responde `¬ M(x)`. Isso é
   exatamente `SAT(R_M x)`. Esse candidato é total, polinomial e um *perfect flip*, então a lei falha. Logo
   `RangeFailureLaw → SAT ∉ P` não pode produzir G21. O fecho de P03 tem 189 módulos e 167 compilam. Os 22
   restantes dependem de `SourceRecovery` (17 erros) e de `P02BehavioralAlignment` (uma `def` mal tipada). O reparo
   **não continua**: o veredito acima torna a rota inútil para G21.
2. **Win-win sobre P03:** a metade que falta equivale ao próprio alvo. O lema genérico está verificado (run
   40137729328, job 121002717293). Relatório: `audit/winwin-20261024/ATK_WINWIN_REPORT.md`, branch
   `atk/winwin-missing-half-audit-20261024`.
3. **Modelo `FinalProofAttack` com codificador arbitrário:** refutado no próprio repositório e substituído pelo
   modelo endurecido.

### 16.5 O que resta

- **G21 (matemática nova).** Um produtor precisa provar que toda DTM endurecida de uma fita, em tempo
  polinomial, erra SAT em alguma entrada. Isso é P ≠ NP no modelo. As técnicas conhecidas esbarram nas barreiras
  de relativização, provas naturais e algebrização.
- **Recíproca de Cook–Levin (formalização).** A implicação `PneqNP → G21` não é necessária para `G21 → PneqNP`.
  Falta uma DTM endurecida que calcule a redução do tableau em tempo polinomial, mais a composição de duas DTMs.
