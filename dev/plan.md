# lean-mqsp 開発計画

目的: mQSP (arXiv:2610.01125) を出発点として，量子アルゴリズムを operator-level で記述し Lean で
証明できる量子プログラミング言語と検証基盤を設計・実装する．同じ言語の上で QSVT (arXiv:1806.01838)
を特殊ケースとして，coherent phase estimation (arXiv:2103.09717) を同じ primitive から記述・証明する．

関連文書: 言語設計 `doc/design.md`，仕様（定理 ID）`dev/formal-spec.md`，
論文調査 `dev/inventory/{mqsp-core,mqsp-algorithms,mqsp-applications,qsvt,cpe}.md`，進捗 `PROGRESS.md`，
エージェント規約 `AGENTS.md`．

## 方針

1. **意味論の核は mQSP の module（unitary junction + oracle ports）**．QSVT の位相列も，回路も，
   すべて module の合成として表す．言語（表面構文）は module の合成規則と library module を
   constructor とする帰納型で，`denote` によって module に写す．
2. **意味論を 4 層に分ける**（証明の合成性のため）:
   (i) steady state（z = 1，代数的）: 伝達関数 `F = A + B Q (1 − D Q)⁻¹ C`，catalyst `Γ`，重み `W_j`；
   (ii) impulse response（時間領域）: 係数 `G_n`（遅延付き），多変数係数 `F_n`；
   (iii) compile: unitary Toeplitz lift `W_N[G]`（明示回路），clock による `Be[G̃_N/α]`，クエリ数；
   (iv) approximation: `‖G̃_N − F‖ ≤ ε`（clock shaping）と resource accounting．
   各合成規則（Series, DirectSum, Spectator, Wire, Close, Substitute, Delay, Inverse, Project）について
   (i)–(iv) の合成定理を証明する．
3. **代数的・有限的な定理を先に，解析的な定理は最小のきれいな形で**．Toeplitz lift の正しさ，
   unitary kernel identity，合成規則，QSVT 定理は有限次元線形代数で閉じる．clock shaping は
   「係数の裾の評価 ⟹ clock 誤差評価」と「解析的増大度 ⟹ 裾の評価（Cauchy 評価）」に分離する．
4. **sorry なし，axiom なし**で main に入れる．未証明の定理は仕様書に「未着手」として残し，
   Lean には書かない（`sorry` 付きで main に入れない）．
5. **subagent の使い方**: 論文調査・定理インベントリ，モジュールごとの実装（互いに素なファイル集合），
   テスト追加を並列に委任する．設計・仕様・レビュー・コミットは親セッションが行う．
6. **ビルド**: Mathlib v4.34.1 のキャッシュを使う（`lake exe cache get`）．doc-gen4 等は使わない．

## ディレクトリ（予定）

```
MQSP/
  Core/        HSpace, DSum（直和・ブロック作用素）, PiSum（ポート直和）, Reg（レジスタ）, 
               BlockEncoding, Norms（作用素ノルム補題）
  Module/      OracleSig, Module（system matrix + ports + delays）, SteadyState（F, Γ, W），
               Coeff（多変数係数 F_n, Γ_n），Impulse（遅延付き G_n）
  Transfer/    unitary kernel identity（Thm 2.1），contractivity，catalyst identities
  Compose/     Wire, Series, DirectSum, Spectator, Close, Substitute, Delay, Inverse, Project
  Compile/     Circuit（回路 IR とクエリ数），ToeplitzLift（Thm 2.2），Clock（Thm 2.3, Lemma 2.4），Quditize
  Clock/       Transient（Eq 1.12），Uniform（Thm 3.2/Lemma 3.3），Flat（Lemma 3.5），Analytic（Thm 3.9 系）
  Modules/     Query, AP1, Cayley, WeightedCayley, HermitianDilation, ReflectionWalk, PrepQuery,
               FPAATap, SignLattice, Exp, HamSim, Reciprocal, StatePrep
  Algorithms/  FPAA, OAA, Threshold, HamSim, WeightedHamSim, StatePrep, QLSP, ...
  Poly/        多項式近似ライブラリ（parity, sup norm, Chebyshev, sign/threshold/exp 近似）
  QSVT/        QSP/QSVT を module の特殊ケースとして: PhaseSeq, QSVT 定理, 実多項式 LCU, 
               block-encoding 算術, GSLW のアルゴリズム
  CPE/         coherent phase/energy/amplitude estimation (Rall) の primitive と構成
  Lang/        表面構文 Prog，denote，cost，#mqsp_info
  Resource/    Def A.1 の資源勘定（per-oracle cost，weighted cost，ancilla/dimension）
test/          lake test
doc/           design.md（設計），language.md（使い方）
dev/           plan, formal-spec, inventory/, survey notes
```

## マイルストーン

- **M0 準備**（完了見込み: 初日）: Lean プロジェクト，Mathlib キャッシュ，Core（HSpace/DSum/PiSum），
  論文調査（5 本のインベントリ），設計書 v1，仕様書 v1．
- **M1 module と steady state**: OracleSig/Module/SteadyState，Prop 5.1（unitary junction），
  Thm 2.1 の z=1 版（F unitary，Γ の保存則，重みの合成則 Eq 5.15），合成規則 (i) 層の定理．
- **M2 compile**: 回路 IR，Toeplitz lift（Thm 2.2）とクエリ数 Eq 2.24，Toeplitz 縮小性 Eq 2.26，
  clock factorization（Thm 2.3 の構成方向，Lemma 2.4），`Be[G̃_N/α]` の定理．
- **M3 library modules と QSVT**: Query/Cayley/Exp/FPAA/Sign の module と steady value；
  QSP 位相列 = Series(Wire;Query) の module，QSVT 定理（GSLW Thm 17/Cor 18）を module の
  steady value として証明，endpoint clock による compile = QSVT 回路；block-encoding 算術．
- **M4 approximation**: transient identity，uniform clock，flat clock，解析的裾評価（Cauchy），
  HamSim/FPAA の有限 N の誤差評価；Poly ライブラリの近似定理．
- **M5 algorithms**: 重み付き HamSim（Thm 6.1 の operator-level），StatePrep，Threshold，QLSP の
  reciprocal など，可能なものから operator-level の正しさ + クエリ数を形式化．
- **M6 CPE**: 位相/エネルギー信号の block encoding，1 bit 抽出，coherent iteration，振幅推定の
  primitive を同じ基盤で形式化．
- **M7 言語層**: Prog/denote/cost，`#mqsp_info`，使い方文書，PR．

各マイルストーンの終わりに `lake build`・`lake test` を通し，`PROGRESS.md` に記録，`ss` に commit．
ひと段落（M3 または M4 以降の安定点）で main への PR を作る．

## リスクと対応

- Mathlib に SVD/核ノルムがない: clock は「明示的な因数分解 `X = Σ s_ℓ a_ℓ b_ℓ†`」を入力とする
  構成的定式化にし，核ノルム最小性（Thm 2.3 の only-if）は optional にする．
- 作用素値解析関数の Cauchy 評価: Mathlib の `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
  （Banach 空間値）を使う．Abel 極限は `Mathlib.Analysis.Complex.AbelLimit`．
- テンソル積: Mathlib の内積空間テンソル積は使わず，直和モデル（`Fin N → E`）で統一する．
- 規模: 論文の定理数（mQSP 約 200，QSVT 約 60，CPE 約 20）に対し，primitive-level を優先し，
  application は operator-level の正しさとクエリ数に限定する．
