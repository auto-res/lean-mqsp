# PROGRESS

進捗ログ（新しいものを上に）．計画は [dev/plan.md](dev/plan.md)，設計は [doc/design.md](doc/design.md)，
仕様 ID は [dev/formal-spec.md](dev/formal-spec.md)，論文調査は [dev/inventory/](dev/inventory/) を参照．

## 2026-10-10 (2) — M1/M2: 接続規則，Toeplitz lift（Thm 2.2），clock，最小ノルム catalyst，Cayley

- **接続規則（`MQSP/Compose/`）**: Series（`F₂F₁`，`Γ₁ ⊕ Γ₂F₁`，重み (5.15)），Wire（前後の既知ゲート），
  DirectSum（`F₁ ⊕ F₂`），Spectator（`1 ⊗ F`），Inverse（`S†`, `O†` ⟹ `F†`，`Γ_inv = QΓF†`）をすべて sorry なしで証明．
  regular 性は有限次元の単射性で合成し，catalyst は不動点方程式の一意解（`catalyst_unique`）として特定する方式が有効だった．
- **Toeplitz lift（`MQSP/Compile/Lift.lean`，mQSP Thm 2.2）**: 遅延バッファ `Mem = ⊕ⱼ Reg rⱼ Kⱼ`，埋め込み `J k`
  （clock `|k⟩`，slot `k mod rⱼ`），`r_j ∣ k` のときだけポート `j` を呼ぶ `oracleAt`，`lift = Π (step k ∘ oracleAt k)`．
  **`toeplitz_block`**: public ブロック `(o,i)` は `G (o−i)`（`i ≤ o`），**`queries_eq`**: `⌊(N−1)/rⱼ⌋`，`norm_G_le_one`（Eq 2.26）．
  証明は「slot の内容 = 書き込みからの経過時間と oracle 適用済みフラグ」の不変量による時刻帰納法．
- **clock（`MQSP/Compile/Clock.lean`，Thm 2.3 構成方向・Lemma 2.4）**: clock 状態の等長 `clockIn`，
  `clockOut_map_clockIn`（選択ブロック = `L_X(kernel)`），`extract_toeplitz`（`Σ c_n(X) G_n`），
  `norm_extract_le`（因数分解版 Lemma 2.4），`isEncodingOf_quditize`．
- **`MQSP/Core/BlockEncoding.lean`**: 等長の対による符号化 `IsEncodingOf U Vin Vout A`（GSLW Def 11 と clock 選択ブロックを統一）．
- **最小ノルム catalyst（`MQSP/Module/Steady.lean`）**: 調査（mqsp-core §5.2 G2）の指摘どおり，`S`,`Q` ユニタリなら
  `ran C ⊆ ran(1−DQ)` で定常解は常に存在．`catalyst₀`（`ker(1−DQ)` に直交する一意解）を定義し，`isUnitary_steady₀` を
  regular 仮定なしで証明．regular なら `catalyst₀ = catalyst`．
- **transient（`MQSP/Clock/Transient.lean`，Eq 1.12）**: Abel 和による恒等式と clock 誤差評価 S1．
- **Cayley module（`MQSP/Modules/Cayley.lean`，Eq 1.24/5.35）**: self-inverse block encoding に対し regular，
  `steady = (1 − iA)(1 + iA)⁻¹`，固有ベクトル上の重み `2/(1+x²)`（Eq 1.27）．
- 進行中（subagent）: SVD 不要の QSVT 定理（`QSVT/Core.lean`，2 ブロック漸化式），chain junction（有限 query 回路），
  oracle 比較恒等式 (2.14)，signal 正規化（反射 walk，Hermitian dilation），生成関数と Cauchy 裾評価，資源勘定，LCU．
- 規模: Lean 約 5,000 行（証明済み部分），`lake build`/`lake test` 成功，公理は標準 3 つ．

## 2026-10-09 (1) — M0: プロジェクト準備，Core と Junction

- Lean 4.34.1 + Mathlib v4.34.1（キャッシュ利用，ソースビルドなし）．`lake build`/`lake test` 成功．
- `MQSP/Core/HSpace.lean`: 有限次元複素 Hilbert 空間の束 `HSpace`，`IsUnitary`/`IsIsometry`/`IsProj`，
  有限次元では等長 ⟹ ユニタリ，反射 `2P−1` のユニタリ性．
- `MQSP/Core/DSum.lean`: 直和 `P ⊕ₕ L = WithLp 2 (P × L)`，`inl/inr/fst/snd` と随伴，2×2 ブロック作用素
  `block A B C D` の代数（合成・随伴・分解・外延性）．
- `MQSP/Core/PiSum.lean`: ポート直和 `PiSum K = PiLp 2 K`，`proj/single`，対角作用素 `diag O` とそのユニタリ性．
- `MQSP/Module/Defs.lean`: 抽象ポート構造 `Ports L K`（coisometry の族），feedback `Q = Σ πᵢ† Oᵢ πᵢ`，
  **unitary junction** `Junction P L K`（system matrix `S`，ports，delays），ブロック `A B C D` と
  ユニタリ性の 8 恒等式，regular（`1 − DQ` 可逆）のときの catalyst `Γ`，steady value `F = A + B Q Γ`，
  定常方程式 (2.7)，ノルム保存 (2.10)，**`isUnitary_steady`（Prop 5.1 / Thm 2.1 の z=1 版）**，重み `W_j`．
- 論文調査: 5 本のインベントリを subagent に委任（mqsp-core, mqsp-algorithms, mqsp-applications, qsvt, cpe）．
  `mqsp-applications.md` 完了（§7–8 は時変 system を基本にした因果 lift の一般化を提案）．
