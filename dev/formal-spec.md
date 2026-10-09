# lean-mqsp 形式化仕様（定理 ID 一覧）v1

各項目は `ID. 名称 — 内容（論文の対応）— Lean の宣言（予定/済）— 状態`．
状態: ✅ 証明済（sorry なし）/ 🔶 文のみ（sorry）/ ⬜ 未着手．
論文の番号は mQSP = arXiv:2610.01125 v1，GSLW = arXiv:1806.01838 v1，Rall = arXiv:2103.09717 v4．
詳細なインベントリは `dev/inventory/`．

## CORE（`MQSP/Core`）

- CORE-1. `HSpace`，`IsUnitary/IsIsometry/IsProj`，等長 ⟹ ユニタリ（有限次元），反射のユニタリ性 — `Core/HSpace.lean` ✅
- CORE-2. 直和 `P ⊕ₕ L`，`inl/inr/fst/snd`，`block A B C D` の代数（合成・随伴・分解・外延性） — `Core/DSum.lean` ✅
- CORE-3. ポート直和 `PiSum K`，`proj/single`，`diag O` とユニタリ性 — `Core/PiSum.lean` ✅
- CORE-4. 恒等拡張 `extendR/extendL`（作用・ノルム・ユニタリ性・合成・随伴） — `Core/Extend.lean` ✅
- CORE-5. レジスタ `Reg n E`，`single/proj/map` — `Core/Reg.lean` ✅
- CORE-6. block encoding: `IsEncodingOf U Vin Vout A`（等長の対；mQSP Eq 1.16，GSLW Def 11/43），随伴・等長との合成・縮小性 — `Core/BlockEncoding.lean` ✅
- CORE-7. spectral mapping（連続汎関数計算）: `‖P(A)‖ ≤ sup|P|`，`‖P(A) − f(A)‖ ≤ sup|P − f|`，固有ベクトル評価 — `Core/Spectral.lean` ✅

## MOD（`MQSP/Module`）

- MOD-1. `Ports L K`（coisometry 族），`feedback Q = Σ πⱼ† Oⱼ πⱼ`（mQSP Eq 2.2），`Junction P L K` — `Module/Defs.lean` ✅
- MOD-2. regular なら catalyst `Γ = (1−DQ)⁻¹C`，`steady F = A + BQΓ`，定常方程式 (2.7)，ノルム保存 (2.10)，
  **`F` ユニタリ**（Prop 5.1 / Thm 2.1 の z=1 版），重み `Wⱼ = ‖πⱼΓψ‖²` (2.8) — `Module/Defs.lean` ✅
- MOD-2b. 一般化: 定常解は常に存在（`ran C ⊆ ran(1−DQ)`，S と Q のユニタリ性から），最小ノルム解として catalyst を定義，
  F は解に依らない，`isUnitary_steady₀` — `Module/Steady.lean` ✅
- MOD-3. 時間領域 impulse response `gseq`, `fb`, `G`（遅延付き Eq 2.20/2.21），unit delay の閉形式 `G(n+1) = BQ(DQ)ⁿC` —
  `Module/Impulse.lean` ✅
- MOD-4. 多変数係数 `F_n`（Eq 2.3）と `G_n = Σ_{⟨r,m⟩=n} F_m`（解析層で使用） — ⬜
- MOD-5. oracle 置換の比較 (2.14) `1 − F′†F = Γ′†(1 − Q′†Q)Γ` と query-Lipschitz 評価 — `Module/Compare.lean` ✅；(2.11)/(2.12)/(2.13) の z 微分版 — ⬜

## COMP（`MQSP/Compose`，mQSP §5.2）

- COMP-1. `Ports.sum`（`L₁ ⊕ₕ L₂` のポート），`OracleTuple.left/right/sum` — `Compose/Series.lean` ✅
- COMP-2. Series: `S = (S₂ ⊕ 1)(S₁ ⊕ 1)`，ブロック公式，regular の遺伝，`Γ₂₁ = Γ₁ ⊕ Γ₂F₁` (4.103)，`F₂₁ = F₂F₁` (4.102)，
  重み (5.15) — `Compose/Series.lean` ✅
- COMP-3. Wire（前後の既知ユニタリ）: `F V`, `V F` — `Compose/Wire.lean` ✅
- COMP-4. DirectSum: `F₁ ⊕ F₂`，`W₁ ⊕ W₂` — `Compose/DirectSum.lean` ✅
- COMP-5. Spectator: `1_R ⊗ F` — `Compose/Spectator.lean` ✅
- COMP-6. Close（public sector を既知ユニタリで閉じる；steady = Schur 補元 `F_pp + F_pe V (1 − F_ee V)⁻¹ F_ep`，正則性） — `Compose/Close.lean` ✅
- COMP-7. Substitute（module の port への代入）: steady = 外側の steady に `F_B` を代入，catalyst/重みの入れ子 — `Compose/Substitute.lean` ✅
- COMP-8. Inverse（`S†`, `O†` ⟹ `F†`，`Γ_inv = QΓF†`） — `Compose/Inverse.lean` ✅；Project（`Vout† F Vin`），LCU（`|+⟩` flag で `(F₁+F₂)/2`） — `Compose/Project.lean` ✅；Delay（`withDelay`） — `Compose/Delay.lean` ✅
- COMP-9. ポートの併合（同一 oracle の複数コピーを 1 ポートに；クエリ数の勘定） — ⬜

## COMP-C（`MQSP/Compile`，mQSP §2.2–2.3）

- COMP-C1. Toeplitz lift: `Mem`, `LiftSpace`, `slot`, `embedL`, `J`, `step`, `oracleAt`, `liftUpTo`, `lift`；
  ユニタリ性；`queries = ⌊(N−1)/rⱼ⌋` (2.24)；**public ブロック = `T_N[G]`**（Thm 2.2）；`‖G_n‖ ≤ 1` (2.26) —
  `Compile/Lift.lean` ✅
- COMP-C2. clock: 因数分解 clock `X = Σ s_ℓ a_ℓ b_ℓ†`，`c_n(X)`, `L_X(E)`，`‖L_X(E)‖ ≤ ‖X‖_* ‖E‖`（Lemma 2.4），
  入出力 clock 等長 `clockIn` と `clockOut_map_clockIn`，`extract_toeplitz`，`isEncodingOf_quditize` — `Compile/Clock.lean` ✅
- COMP-C3. 時変 causal lift（Prop 8.1）と定数系列の特殊化 — ⬜（optional）
- COMP-C4. endpoint clock `X = |T⟩⟨0|`: `G T` の厳密な符号化，chain の直接 compile — `Compile/Endpoint.lean` ✅

## CLK（`MQSP/Clock`，mQSP §3）

- CLK-1. transient `K_n = G†(G − Σ_{k≤n} G_k)`，恒等式 (1.12)/(3.14)，S1: `‖G − Σ c_n G_n‖ ≤ |1−c₀| + Σ|c_n − c_{n+1}|‖K_n‖` — `Clock/Transient.lean` ✅
- CLK-2. uniform clock（Thm 3.2，Lemma 3.3）: `stepResp_eq`，エネルギー不等式，`‖F − G̃_N‖ ≤ ‖Γ‖/√N`，end-to-end `isEncodingOf_uniform` — `Clock/Uniform.lean` ✅；OAA 版（Prop 3.4） — ⬜
- CLK-3. 箱型 flat clock（正規化 √(1+D/L)，S4） — `Clock/Flat.lean` ✅；最適 flat clock（Lemma 3.5） — ⬜
- CLK-4. 生成関数 `genFun`，大域半径版 Cauchy 評価 `‖G_n‖ ≤ M′/rⁿ`，幾何的裾評価（S7） — `Clock/Analytic.lean` ✅
- CLK-5. 解析的 clock shaping（Thm 3.9，Cor 3.10，Thm 1.1；対数座標版） — ⬜（難）
- CLK-6. 比較安定性（Prop 3.17），構成的 compile（Thm 3.18） — ⬜

## RES（`MQSP/Resource`，mQSP Def A.1，App A）

- RES-1. `CostModel`（ポート→oracle 型，コスト），`weightedCost`，`invocations` — `Resource/Cost.lean` ✅
- RES-2. 正規化と近似誤差（Lemma A.2），条件付き状態（Lemma A.3），OAA のブロック恒等式と誤差（Lemma A.4） — `Resource/Approx.lean` ✅；誤差予算 (A.13) — ⬜
- RES-3. 重み付き遅延配分（Lemma 3.12 の Cauchy–Schwarz 形，Eq 1.18） — `Resource/Allocation.lean` ✅
- RES-4. hybrid argument（縮小作用素の合成誤差は和，`q` 回実行で `qη`；Eq A.13） — `Resource/Hybrid.lean` ✅

## LIB（`MQSP/Modules`，mQSP §5.1/5.3）

- LIB-0. chain junction（有限 query 回路 = module；`D` 冪零，steady = 回路，`G` は遅延 `d` に集中，重み 1/port） — `Modules/Chain.lean` ✅
- LIB-1. Query（`F = O`） — `Modules/Query.lean` ✅；Cayley（Eq 1.24/5.35，`F = (1−iA)(1+iA)⁻¹`，重み `2/(1+x²)`） — `Modules/Cayley.lean` ✅；WeightedCayley（Lemma 5.2，`CayleyData.steady_eq`） — `Modules/WeightedCayley.lean` ✅；AP1 — ⬜
- LIB-2. ReflectionWalk (5.13)，HermitianDilation (5.12) — `Modules/Signals.lean` ✅；PreparationQuery (5.14) — `Modules/PrepQuery.lean` ✅
- LIB-3. FPAA tap (1.38): 定常値 1，catalyst (1.39)，重み `(1−c)/((1+c)sin²θ)` — `Algorithms/FPAA.lean` ✅；有限 N 残差評価 (1.42a) は under-damped 条件 `(1+c)²cos²2θ ≤ 4c` が必要（無条件では反例あり） — ⬜；AP1（Blaschke，Eq 4.66–4.70，gap 評価） — `Modules/AP1.lean` ✅
- LIB-4. Sign lattice (5.27)–(5.30)，Threshold (5.33) — ⬜
- LIB-5. Exp の仕様 `IsExpModule` と HamSim = Exp[WeightedCayley] の理想定常値 `exp(−τM)`（`hamSim_steady`），クエリ数 — `Algorithms/HamSim.lean` ✅；有限 Schur 実現（Thm 5.6 (i)），Prop 5.5 — ⬜
- LIB-6. Reciprocal（Lemma 5.7），StatePrep（Cor 5.8） — ⬜

## ALG（`MQSP/Algorithms`，mQSP §6）

- ALG-1. 重み付き Hamiltonian simulation（Thm 6.1 の ideal 部: `F(1) = e^{−itH}`, 群遅延，`qⱼ`） — ⬜
- ALG-2. StatePrep（Cor 5.8 / Thm 6.5 の ideal 部） — ⬜
- ALG-3. QLSP の骨格（nullspace reflection，Lemma D.1/D.2，Thm 6.7/Cor 6.9 の operator-level） — ⬜
- ALG-4. 再利用補題 D.8（Cayley junction の不変空間），D.10，D.12，D.18 — ⬜

## QSVT（`MQSP/QSVT`，GSLW）

- QSVT-1. 位相列 module `qsp` = chain junction（位相作用素と `U, U†` の交互），steady = `U_Φ`，重み 1/port — `QSVT/Module.lean` ✅
- QSVT-2. QSP 構造定理（Thm 3/4，Cor 8/10，Lemma 9），相補多項式（Thm 5，Lemma 6）: **`exists_phases`**（`1 ≤ n`），scalar 橋渡し `qspPoly_reverse`，Chebyshev 位相，摂動 — `QSP/*`, `QSVT/Phases.lean` ✅（lean-qsvt からの port）
- QSVT-3. **QSVT 定理**（Thm 17）: 2 ブロック漸化式 `Shape`，`proj_UΦ_proj_odd/even`（`A p_Φ(A†A)` / `Π p_Φ(A†A) Π`，SVD なし），
  `pqΦ_neg`（Cor 18 の共役），次数評価 — `QSVT/Core.lean` ✅；Cor 18 の LCU 形 — `QSVT/RealPoly.lean` ✅；endpoint clock での compile — `Compile/Endpoint.lean` ✅
- QSVT-4. block-encoding 算術: Lemma 52（LCU），Lemma 53（積），Lemma 54（テンソル），Cor 55，Thm 56 — ⬜
- QSVT-5. 摂動（Lemma 22/23，Thm 73）＝ query-Lipschitz（mQSP (2.14) の回路版） — ⬜
- QSVT-6. Hermitian 符号化の QSVT `Pr U_Φ Pr = P_Φ(A)` と近似定理（`QSVT/Hermitian.lean`），**synthesis 定理** `exists_qsvt_approx_odd`（`QSVT/Synthesis.lean`） ✅；個別応用（Thm 27/28/30/31/41/58）の operator-level — ⬜（OAA ブロック恒等式は `Resource/Approx.lean` ✅）
- POLY-1. parity，`BoundedOn`，`ApproxOn`，`evenCore/oddCore`，Chebyshev の有界性・parity，縮尺補題 — `Poly/Basic.lean` ✅
- POLY-2. Weierstrass による parity 付き近似多項式の存在，sign 近似（Lemma 25 の存在形），増幅多項式（Rall Lemma 11） — `Poly/Approx.lean` ✅
- POLY-*. 多項式近似（Lemma 25 sign，29，35，40，57 Jacobi–Anger，59，61，65，70，Thm 63/68…） — ⬜

## CPE（`MQSP/CPE`，Rall；詳細は `dev/inventory/cpe.md`）

- CPE-0. ベクトルレベルの近似実装述語 `ApproxImpl ε M W S`，単調性，stitching（Lemma 7），uncompute（Lemma 3/8） — `CPE/Stitch.lean` ✅；rounding promise（丸め規約）とビット，`cos²` 分離 — `CPE/Estimator.lean` ✅
- CPE-1. 位相信号の block encoding: `I` と制御 `U^{2^k}` の LCU（Hadamard test）で `(1 + e^{2πiλ})/2 = cos(πλ) e^{iπλ}`；
  固有ベクトル上の作用 `e^{iθ/2}cos(θ/2)`，`A†A = cos²(θ/2)` — `CPE/Signal.lean` ✅；エネルギー信号 — ⬜
- CPE-2. 1 ビット抽出: 増幅多項式 `A_{η→δ}`（Poly-Sign の変換）を偶多項式として `qsp`（Cor 18）で適用し，
  固有空間上のスカラー評価（`proj_UΦ_plus_eigen`） — `CPE/Signal.lean` ✅；1 ビット抽出 `bit_extraction` — `CPE/Estimator.lean` ✅；読み出し `readout_zero/one`（答え qubit の構造 `s•plus ψ + t•minus ψ`） — `CPE/Readout.lean` ✅；作用素誤差への持ち上げ — ⬜
- CPE-3. coherent iteration（Thm 12）: stitching（Lemma 7：前条件つき近似写像の逐次合成，誤差 δ2^{−k−1}），
  uncompute（Lemma 3/8：copy + inverse，ベクトル版 2ε），クエリ数 `2^{n−k−1}·2M` の勘定 — ⬜
- CPE-4. エネルギー推定（Thm 15）: Jacobi–Anger の `cos` 近似（GSLW Lemma 57/59）と `A∘p_cos²`（縮尺が必要） — ⬜
- CPE-5. 振幅推定（Thm 19/Cor 20）: block-measurement，`U_A† · CNOT · U_A` サンドイッチ恒等式 — ⬜
- CPE-6（optional）. チャネル層（CPTP，部分トレース，トレースノルム）と Prop 18 / Cor 16, 20 の promise なし版 — ⬜

## LANG（`MQSP/Lang`）

- LANG-1. `Prog P pf`（`withDelay` 含む），`denote`，`steady/weight/G/lift/queries`，合成的意味論，記法，`describe`/`numPorts`，program-level compile 定理 — `Lang/Prog.lean` ✅；`#mqsp_info` — `Lang/Info.lean` ✅；例 — `Lang/Examples.lean` ✅
