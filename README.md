# lean-mqsp

Multivariate Quantum Signal Processing (mQSP, [arXiv:2610.01125](https://arxiv.org/abs/2610.01125))
を出発点に，量子アルゴリズムを **operator-level の module ネットワーク**として記述し，
その正しさ・近似誤差・oracle ごとのクエリ複雑さを **Lean 4 + Mathlib** で合成的に証明するための
量子プログラミング言語と形式検証基盤です．
QSVT（[arXiv:1806.01838](https://arxiv.org/abs/1806.01838)）は同じ言語の特殊ケースとして，
coherent phase estimation（[arXiv:2103.09717](https://arxiv.org/abs/2103.09717)）の primitive も
同じ基盤の上に形式化します．

- **言語設計: [doc/design.md](doc/design.md)**，使い方: [doc/language.md](doc/language.md)
- 計画: [dev/plan.md](dev/plan.md)，形式化仕様（定理 ID）: [dev/formal-spec.md](dev/formal-spec.md)
- 論文の定理インベントリと依存グラフ: [dev/inventory/](dev/inventory/)
- 進捗ログ: [PROGRESS.md](PROGRESS.md)

## 中心概念

mQSP の **unitary junction**（既知ユニタリ `S = [[A,B],[C,D]]` を public 空間 `P` と private 空間 `L` の
直和に置き，private のポートに oracle `Oⱼ` をフィードバック接続する）が言語の唯一の primitive です．

```
Junction P L K   -- S : P ⊕ₕ L →L[ℂ] P ⊕ₕ L（ユニタリ），ports : Ports L K（ポート分解），delay : ι → ℕ
steady M O       -- 定常値 F = A + B Q (1 − D Q)⁻¹ C（ユニタリ，mQSP Prop 5.1）
catalyst / weight  -- catalyst Γ とポートごとの Las Vegas 重み ‖πⱼ Γ ψ‖²
G M O n          -- impulse response（遅延付き）
lift M O N       -- unitary Toeplitz lift（mQSP Thm 2.2）: public ブロック = T_N[G]，queries = ⌊(N−1)/rⱼ⌋
```

接続規則 Series / Wire / DirectSum / Spectator / Inverse / Substitute / Delay / Project (LCU) に
定常値・catalyst・重みの合成定理があり，表面言語 `MQSP.Prog`（`p ;; q`, `p ⊕ₚ q`, `p[j ≔ q]`, …）の
`denote` がそれらを束ねます．

## ディレクトリ

- `MQSP/Core/` — Hilbert 空間（`HSpace`），直和とブロック作用素，ポート直和，レジスタ `Reg n E`，
  block encoding（`IsEncodingOf`），spectral mapping（連続汎関数計算）
- `MQSP/Module/` — `Ports`，`Junction`，定常状態（regular 版と最小ノルム版），impulse response，oracle 比較
- `MQSP/Compose/` — 接続規則（Series, Wire, DirectSum, Spectator, Inverse, Substitute, Delay, Project/LCU）
- `MQSP/Compile/` — Toeplitz lift（Thm 2.2），clock 状態と kernel 抽出（Thm 2.3/Lemma 2.4），endpoint clock
- `MQSP/Clock/` — transient 恒等式（Eq 1.12），箱型 clock，uniform clock の end-to-end 定理（Thm 3.2），
  生成関数と Cauchy 評価
- `MQSP/Modules/` — Query, Cayley, WeightedCayley（Lemma 5.2），chain（有限 query 回路），反射 walk / Hermitian dilation
- `MQSP/Algorithms/` — Hamiltonian simulation の理想ネットワーク `Exp ∘ WeightedCayley`（仕様/実装分離）
- `MQSP/QSVT/` — SVD 不要の QSVT 定理（GSLW Thm 17），Cor 18，位相列 module，endpoint 回路
- `MQSP/CPE/` — 位相信号の block encoding，固有空間ごとのビット抽出，近似実装の stitching / uncompute
- `MQSP/Poly/` — parity 付き多項式，Chebyshev，Weierstrass による近似多項式の存在（sign，増幅多項式）
- `MQSP/Resource/` — Def A.1 の資源勘定（重み付きクエリコスト）
- `MQSP/Lang/` — 表面言語 `Prog`，`denote`，合成的意味論
- `test/` — `lake test`（公理監査 `#print axioms`，言語のスモークテスト）

## ビルド

```sh
lake exe cache get   # Mathlib v4.34.1 のキャッシュ（必須）
lake build
lake test
```

公理は `propext`, `Classical.choice`, `Quot.sound` のみ．`sorry` なし（main 時点）．

## 主要な結果

| 内容 | 定理 | ファイル |
|---|---|---|
| 定常値のユニタリ性（mQSP Prop 5.1）: regular 版・最小ノルム版 | `isUnitary_steady`, `isUnitary_steady₀` | `Module/Defs.lean`, `Module/Steady.lean` |
| Series の合成則 `F₂F₁`, `Γ₁ ⊕ Γ₂F₁`, 重み (5.15) | `series_steady`, `series_catalyst`, `series_weight_*` | `Compose/Series.lean` |
| Substitute（入れ子）: steady = 外側に `F_B` を代入 | `subst_steady`, `subst_weight_inr` | `Compose/Substitute.lean` |
| **Toeplitz lift（Thm 2.2）**: public ブロック = `T_N[G]`，`queries = ⌊(N−1)/rⱼ⌋` | `toeplitz_block`, `queries_eq` | `Compile/Lift.lean` |
| clock 抽出（Thm 2.3 構成方向，Lemma 2.4） | `clockOut_map_clockIn`, `norm_extract_le` | `Compile/Clock.lean` |
| transient 恒等式（Eq 1.12）と誤差評価 | `steady_adj_sub_weighted` | `Clock/Transient.lean` |
| **uniform clock の end-to-end compile（Thm 3.2）**: 誤差 `‖Γ‖/√N`，正規化 1 | `isEncodingOf_uniform` | `Clock/Uniform.lean` |
| oracle 比較恒等式 (2.14) と query-Lipschitz 評価 | `norm_steady_sub_steady_le` | `Module/Compare.lean` |
| Cayley module: steady = `(1−iA)(1+iA)⁻¹`，重み `2/(1+x²)` | `cayley_steady`, `cayley_weight_eigen` | `Modules/Cayley.lean` |
| Cayley junction with load（Lemma 5.2） | `CayleyData.steady_eq` | `Modules/WeightedCayley.lean` |
| **QSVT（GSLW Thm 17，SVD なし）**: `Π′U_ΦΠ = A p_Φ(A†A)` | `proj_UΦ_proj_odd/even` | `QSVT/Core.lean` |
| 実多項式（Cor 18）: `(U_Φ + U_{−Φ})/2` | `proj_average_proj_odd` | `QSVT/RealPoly.lean` |
| QSP 位相列 = chain module，endpoint clock で厳密 compile | `qsp_steady`, `isEncodingOf_chain_endpoint` | `QSVT/Module.lean`, `Compile/Endpoint.lean` |
| spectral mapping: `|P−f| ≤ ε` on `[−1,1]` ⟹ `‖P(A) − f(A)‖ ≤ ε` | `norm_polyCalc_sub_cfc_le` | `Core/Spectral.lean` |
| sign / 増幅多項式の存在（Weierstrass） | `exists_sign_approx`, `exists_amplifier` | `Poly/Approx.lean` |
| CPE: 位相信号 `(1+U)/2`，固有空間上のビット抽出 `p_Φ(cos²(θ/2))` | `proj_UΦ_plus_eigen` | `CPE/Signal.lean` |
| CPE: stitching / uncompute（Lemma 7, 3/8） | `ApproxImpl.comp`, `ApproxImpl.uncompute` | `CPE/Stitch.lean` |
