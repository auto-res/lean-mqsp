# lean-mqsp 形式化仕様（定理 ID 一覧）v1

各項目は `ID. 名称 — 内容（論文の対応）— Lean の宣言（予定/済）— 状態`．
状態: ✅ 証明済（sorry なし）/ 🔶 文のみ（sorry）/ ⬜ 未着手．
論文の番号は mQSP = arXiv:2610.01125 v1，GSLW = arXiv:1806.01838 v1，Rall = arXiv:2103.09717 v4．
詳細なインベントリは `dev/inventory/`．

## CORE（`MQSP/Core`）

- CORE-1. `HSpace`，`IsUnitary/IsIsometry/IsProj`，等長 ⟹ ユニタリ（有限次元），反射のユニタリ性 — `Core/HSpace.lean` ✅
- CORE-2. 直和 `P ⊕ₕ L`，`inl/inr/fst/snd`，`block A B C D` の代数（合成・随伴・分解・外延性） — `Core/DSum.lean` ✅
- CORE-3. ポート直和 `PiSum K`，`proj/single`，`diag O` とユニタリ性 — `Core/PiSum.lean` ✅
- CORE-4. 恒等拡張 `extendR/extendL`（作用・ノルム・ユニタリ性・合成・随伴） — `Core/Extend.lean` 🔶
- CORE-5. レジスタ `Reg n E`，`single/proj/map` — `Core/Reg.lean` ✅
- CORE-6. block encoding: `IsBlockEncodingOf U V_in V_out A`（V 等長）（mQSP Eq 1.16，GSLW Def 11/43） — ⬜
- CORE-7. 直交射影・2 次元不変部分空間の補題（qubitization） — ⬜

## MOD（`MQSP/Module`）

- MOD-1. `Ports L K`（coisometry 族），`feedback Q = Σ πⱼ† Oⱼ πⱼ`（mQSP Eq 2.2），`Junction P L K` — `Module/Defs.lean` ✅
- MOD-2. regular なら catalyst `Γ = (1−DQ)⁻¹C`，`steady F = A + BQΓ`，定常方程式 (2.7)，ノルム保存 (2.10)，
  **`F` ユニタリ**（Prop 5.1 / Thm 2.1 の z=1 版），重み `Wⱼ = ‖πⱼΓψ‖²` (2.8) — `Module/Defs.lean` ✅
- MOD-2b. 一般化: 定常解は常に存在（`ran C ⊆ ran(1−DQ)`，S と Q のユニタリ性から），最小ノルム解として catalyst を定義，
  F は解に依らない — ⬜（調査 mqsp-core §5.2 G2）
- MOD-3. 時間領域 impulse response `gseq`, `fb`, `G`（遅延付き Eq 2.20/2.21），unit delay の閉形式 `G(n+1) = BQ(DQ)ⁿC` —
  `Module/Impulse.lean` 🔶
- MOD-4. 多変数係数 `F_n`（Eq 2.3）と `G_n = Σ_{⟨r,m⟩=n} F_m`（解析層で使用） — ⬜
- MOD-5. unitary kernel identity (2.11)/(2.16)，微分と catalyst 重み (2.12)/(2.13)，oracle 置換の比較 (2.14) — ⬜

## COMP（`MQSP/Compose`，mQSP §5.2）

- COMP-1. `Ports.sum`（`L₁ ⊕ₕ L₂` のポート），`OracleTuple.left/right/sum` — `Compose/Series.lean` 🔶
- COMP-2. Series: `S = (S₂ ⊕ 1)(S₁ ⊕ 1)`，ブロック公式，regular の遺伝，`Γ₂₁ = Γ₁ ⊕ Γ₂F₁` (4.103)，`F₂₁ = F₂F₁` (4.102)，
  重み (5.15) — `Compose/Series.lean` 🔶
- COMP-3. Wire（前後の既知ユニタリ）: `F V`, `V F` — ⬜
- COMP-4. DirectSum: `F₁ ⊕ F₂`，`W₁ ⊕ W₂` — ⬜
- COMP-5. Spectator: `1_R ⊗ F` — ⬜
- COMP-6. Close（内部フィードバック，Schur 補元 (4.98)–(4.101)，正則性仮定） — ⬜
- COMP-7. Substitute（module の port への代入）: `A_A + B_A F_B (1 − D_A F_B)⁻¹ C_A` — ⬜
- COMP-8. Delay（遅延変更），Inverse（`S†`, `O†` ⟹ `F†`），Project（`V_out† F V_in`） — ⬜
- COMP-9. ポートの併合（同一 oracle の複数コピーを 1 ポートに；クエリ数の勘定） — ⬜

## COMP-C（`MQSP/Compile`，mQSP §2.2–2.3）

- COMP-C1. Toeplitz lift: `Mem`, `LiftSpace`, `slot`, `embedL`, `J`, `step`, `oracleAt`, `liftUpTo`, `lift`；
  ユニタリ性；`queries = ⌊(N−1)/rⱼ⌋` (2.24)；**public ブロック = `T_N[G]`**（Thm 2.2）；`‖G_n‖ ≤ 1` (2.26) —
  `Compile/Lift.lean` 🔶
- COMP-C2. clock: 因数分解 clock `X = Σ s_ℓ a_ℓ b_ℓ†`，`c_n(X)`, `L_X(E)`，`‖L_X(E)‖ ≤ ‖X‖_* ‖E‖`（Lemma 2.4），
  入出力 clock 等長 `V_in, V_out` と `V_out† (1 ⊗ W_N) V_in = L_X(T_N[G])/α`（Thm 2.3 構成方向，Eq 2.31–2.32） — ⬜
- COMP-C3. 時変 causal lift（Prop 8.1）と定数系列の特殊化 — ⬜（optional）
- COMP-C4. endpoint clock `X = |T⟩⟨0|`: 有限 query 回路の実現（Thm 4.4 の構成）— QSVT 埋め込みに使用 — ⬜

## CLK（`MQSP/Clock`，mQSP §3）

- CLK-1. transient `K_n = G†(G − Σ_{k≤n} G_k)`，恒等式 (1.12)/(3.14)，S1: `‖G − Σ c_n G_n‖ ≤ |1−c₀| + Σ|c_n − c_{n+1}|‖K_n‖` — ⬜
- CLK-2. uniform clock（Thm 3.2，Lemma 3.3）と OAA 版（Prop 3.4） — ⬜
- CLK-3. 箱型 flat clock（正規化 √(1+D/L)，S4）と最適 flat clock（Lemma 3.5） — ⬜
- CLK-4. 係数の裾評価 ⟹ clock 誤差（S1 + S2），大域半径版 Cauchy 評価 `‖G_n‖ ≤ M_R R^{−n}`（S7） — ⬜
- CLK-5. 解析的 clock shaping（Thm 3.9，Cor 3.10，Thm 1.1；対数座標版） — ⬜（難）
- CLK-6. 比較安定性（Prop 3.17），構成的 compile（Thm 3.18） — ⬜

## RES（`MQSP/Resource`，mQSP Def A.1，App A）

- RES-1. oracle 型とコスト，ポート→型の対応（方向・多重度），重み付きクエリコスト `⟨C, q⟩` — ⬜
- RES-2. 正規化と近似誤差（Lemma A.2），条件付き状態（Lemma A.3），OAA（Lemma A.4），誤差予算 (A.13) — ⬜

## LIB（`MQSP/Modules`，mQSP §5.1/5.3）

- LIB-1. Query（`F = O`），AP1（Blaschke），Cayley（Eq 1.24，`F = e^{−2i arctan x}`），WeightedCayley（Lemma 5.2） — ⬜
- LIB-2. HermitianDilation (5.12)，ReflectionWalk (5.13)，PreparationQuery (5.14) — ⬜
- LIB-3. FPAA tap (1.38)/(5.24)，Prop 5.3；OAA（Cor 5.4） — ⬜
- LIB-4. Sign lattice (5.27)–(5.30)，Threshold (5.33) — ⬜
- LIB-5. Exp（有限 Schur 実現，Thm 5.6 (i)），HamSim = Exp∘Cayley (5.34)，Prop 5.5 — ⬜
- LIB-6. Reciprocal（Lemma 5.7），StatePrep（Cor 5.8） — ⬜

## ALG（`MQSP/Algorithms`，mQSP §6）

- ALG-1. 重み付き Hamiltonian simulation（Thm 6.1 の ideal 部: `F(1) = e^{−itH}`, 群遅延，`qⱼ`） — ⬜
- ALG-2. StatePrep（Cor 5.8 / Thm 6.5 の ideal 部） — ⬜
- ALG-3. QLSP の骨格（nullspace reflection，Lemma D.1/D.2，Thm 6.7/Cor 6.9 の operator-level） — ⬜
- ALG-4. 再利用補題 D.8（Cayley junction の不変空間），D.10，D.12，D.18 — ⬜

## QSVT（`MQSP/QSVT`，GSLW）

- QSVT-1. 位相列 module `qsp Φ U := Series_k (Wire(e^{iφ_k(2Π−1)}) ; Query U^{(†)})`，`D = 0`，steady = `U_Φ`（Def 15） — ⬜
- QSVT-2. QSP 構造定理（Thm 3/4，Cor 8/10，Lemma 9），相補多項式（Thm 5，Lemma 6） — ⬜
- QSVT-3. **QSVT 定理**（Thm 17）: `Π̃ U_Φ Π = P^{(SV)}(A)`（SVD なし，`y = x²` の帰納），Cor 18（実多項式 = DirectSum+Project），
  Lemma 19（gadget）＝ endpoint clock での compile — ⬜
- QSVT-4. block-encoding 算術: Lemma 52（LCU），Lemma 53（積），Lemma 54（テンソル），Cor 55，Thm 56 — ⬜
- QSVT-5. 摂動（Lemma 22/23，Thm 73）＝ query-Lipschitz（mQSP (2.14) の回路版） — ⬜
- QSVT-6. 応用（Thm 27 FPAA，Thm 28 OAA，Thm 30/31 閾値，Thm 41 擬似逆，Thm 58 HamSim，…）の operator-level — ⬜
- POLY-*. 多項式近似（Lemma 25 sign，29，35，40，57 Jacobi–Anger，59，61，65，70，Thm 63/68…） — `MQSP/Poly` ⬜

## CPE（`MQSP/CPE`，Rall）— CPE 調査完了後に確定

- CPE-1. 位相信号 / エネルギー信号の block encoding — ⬜
- CPE-2. 1 ビット抽出（符号/閾値多項式の `qsp`），確率勘定 — ⬜
- CPE-3. coherent iteration（ビット列レジスタ，rounding promise） — ⬜
- CPE-4. 振幅推定 — ⬜

## LANG（`MQSP/Lang`）

- LANG-1. `Prog`，`denote`，`cost`，`compile`，表面記法，`#mqsp_info` — ⬜
