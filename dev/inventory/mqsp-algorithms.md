# mQSP 論文 §6・付録 C・付録 D の定理インベントリ（多 oracle アルゴリズム）

- 対象: G. H. Low, "Multivariate Quantum Signal Processing", arXiv:2610.01125 (Draft v8.5)。
  範囲は §6 "Multioracle quantum algorithms"、付録 C "Hamiltonian algorithms and weighted state preparation"、
  付録 D "Linear systems, Volterra certificates, and eigenvalue estimation"。§1.2（新アルゴリズムの概観）は文脈として参照。
- 行番号 `@nnnn` は pdftotext 版 `paper.txt` の行（§6: 6568–11311、付録 C: 16496–17279、付録 D: 17280–19243）。
  式番号 `(6.xx)` などは論文の番号。数式は plain-text で書く。
- §2–§5 の核定理（Thm 2.1–2.3、§3 の clock 理論、§5 の module と接続規則）と付録 A/B は別の調査者の担当。
  本書ではそれらを論文番号（`Thm 2.2`, `Lemma 5.2` など）で参照するだけとする。
- 記法: `⟨u,v⟩ = Σ_j u_j v_j`、`⟨u,v⟩_{1/2} = (Σ_j √(u_j v_j))^2`、`‖v‖_1 = Σ_j v_j`、`C_Σ = ‖C‖_1`。
  `Be[X/λ]` は block encoding（`(⟨0|⊗I) U (|0⟩⊗I) = X/λ`）、`T_N[G]` は horizon N の Toeplitz block、
  `q_j` は oracle j の制御付き呼び出し回数（forward と inverse を別々に数える、Def A.1）。

## 0. 凡例

### 0.1 module・接続規則・コンパイルの略記

- §5 のライブラリ module:
  `Query(O)`、`AP1`、`CJ(K0; C_1..C_m; V_1..V_m)` = Lemma 5.2 の一般 Cayley junction
  （load `M(z) = iK0 + Σ_j C_j† [(1−z_j^2)I + 2i z_j V_j]/(1+z_j^2) C_j`、`F0 = (I−M)(I+M)^{-1}`）、
  `WeightedCayley(E; V)` = `CJ(K0 = 0, C_j = √(λ_j/Λ)|0⟩_j)`、
  `Exp_T(w) = exp[−T(1−w)/(1+w)]`（(1.45), §5.3.4）、`HamSim_T = Exp_T ∘ Cayley`（Prop 5.5）、
  `ExpFin_{τ,R}` = Thm 5.6 の有限実現、`Sign_L(·)` = (5.27)–(5.32) と Lemma B.1 の符号 lattice、`Threshold` (5.33)、
  `PrepQuery(U) = V_U = [[0,U†],[U,0]]` (5.14)、`HermDil(V)` (5.12)、`ReflWalk(V)` (5.13)、
  `Reciprocal_d` = Lemma 5.7、`FPAA` = Prop 5.3、`OAA` = Cor 5.4、`StatePrep` = Cor 5.8。
- §5.2 の接続規則: `Wire(V)`、`Series(F1,F2)`（transfer function は `F2 F1`）、`DirectSum`、`Spectator`、
  `Close_E(wV)`、`Substitute(outer; port := inner)`、`BufferedSeries`、`Delay_r`、`Inverse`、`Project(in,out)`。
- コンパイル: `Compile_N[X](G)` = Thm 2.2 の unitary Toeplitz lift と clock 行列 X（Thm 2.3）で
  `Be[G̃_N/α_clk]` を得る操作。`q_j = ⌊(N−1)/r_j⌋`。`Attn(c)` = 既知減衰（Lemma A.2）。
- ★ = §5 にない application-specific module（新規 junction・新規 IIR）。

### 0.2 カテゴリ

`primitive`（module・信号の構成と z=1 での値）／`composition`（接続規則による組立と不変量）／`feedback`
（Close・恒等閉包・Schur 補行列）／`compilation`（lift・clock・gate）／`approximation/error`（解析近傍・
radial exponent・誤差配分）／`query-complexity`（query 数と重み付きコスト）／`application`（最終アルゴリズム）／
`classical-certificate`（古典的に与えられる数値の証明書）／`analysis-aux`（補助的な評価・例）。

### 0.3 難易度と優先度

- 難易度: 1 = 定義展開と有限次元線形代数、2 = 短い行列計算、3 = 複数ステップの評価・ε 配分、
  4 = 解析接続・clock 理論・多層の誤差管理、5 = 多数の層・外部結果・離散化誤差を含む長い証明。
- 優先度: `core` = 言語の primitive library または §6 の hub として最初に形式化すべきもの、
  `derived` = core から組み立てられるもの、`optional` = 古典的証明書・gate count・下界・例など。

## 1. 概要

§6 の各アルゴリズムは「z=1 で必要な変換を決める → 与えられた oracle access に合う module を選ぶ →
再利用 IIR か application-specific な unitary junction で応答を作る → 完成した応答に対して遅延と clock を選び、
一度だけ quditization する」という順序で構成される（@6568–6580）。custom module は既知の unitary system matrix と
oracle port を持つので、実現可能性は Prop 5.1 から従う。

| 節 | アルゴリズム | 解く問題 | oracle と promise | コスト | per-oracle の主結果 | 番号付き主張 |
|---|---|---|---|---|---|---|
| 6.1.1 | 重み付き Hamiltonian simulation | e^{−itH}、H = Σ_{j=1}^m H_j（非可換） | V_j = Be[H_j/λ_j]、V_j^2 = I、λ_j 既知、controlled と inverse | C_j / 呼び出し | Be[G̃_N/(1+δ)]、‖G̃_N − e^{−itH}‖ ≤ ε、q_j = ⌊(N−1)/r_j⌋、Σ C_j q_j ≤ (1+δ) t ⟨C,λ⟩_{1/2} + O(δ^{-2} ‖C‖_1 log(1/ε)) | Thm 6.1 |
| 6.1.2 | SOS phase amplification | H = Σ A_j† A_j ⪰ 0 のとき位相 ±2kJ0 arctan(√(E/Λ)/J0) を持つ U = (I−iρℋ)^J (I+iρℋ)^{-J} | V_j = Be[A_j/√λ_j] と出力射影 Π_out,j（(6.19)）、V_j と V_j† | c_j = C_{V_j} + C_{V_j†} | Σ c_j q_j ≤ (1+δ)(k/√Λ)(Σ_j c_j^{2/3} λ_j^{1/3})^{3/2} + O(δ^{-3}‖c‖_1 log(1/ε))；厳密な位相対には q_j ≥ ⌈k⌉ が必要 | Thm 6.2, Lemma C.1, Prop C.2, C.3 |
| 6.1.3 | 共有 SELECT | 6.1.1 と同じ | V_j = P_j† SEL P_j、SEL = SEL† = SEL^{-1} | C_S（SEL）、c_j = C_{P_j} + C_{P_j†} | C_S q_S + Σ c_j q_j ≤ (2−γ) t (√(Λ C_S) + Σ_j √(λ_j c_j))^2 + O_{inst,δ}(log(1/ε))、q_S = 区間 [1,N−1] 内の r_j の倍数全体の合併の個数 | Thm 6.3 |
| 6.1.4 | 有限実現 | Exp の有限化と回路 | — | — | スペクトル実現の Toeplitz 誤差 (6.50) | （定理なし） |
| 6.1.5 | sparse Hamiltonian simulation | d-sparse H の e^{−itH} | 位置 oracle O_f（in-place 置換）、値 oracle O_H、既知 s_2 ≥ ‖H‖_{1→2}、h_max ≥ max \|H_xy\| | 各 1 呼び出し | Q_f = Q_H = O(t √d s_2 + √(t d h_max log(1/ε)) + log(1/ε)) | Thm 6.4 |
| 6.2 | 重み付き coherent state summation | \|Ψ⟩ = Σ_j a_j \|ψ_j⟩ / s | U_j\|0⟩ = λ_j\|0⟩_f\|ψ_j⟩ + bad、λ_j ∈ [λ_0j, 1]、s ≥ s_0 > 0 | C_j（U_j、U_j†） | Σ C_j q_j = O([(Σ_j √(\|a_j\| C_j/λ_0j))^2 / s_0 + Σ_j C_j/λ_0j] log(1/ε))；s 既知なら O((Σ…)^2/s + log(1/ε) Σ_j C_j/λ_0j) | Thm 6.5, Lemma 6.6 |
| 6.3 | 多 oracle QLSP | A^{-1}b/‖A^{-1}b‖、A = Σ A_j、b = Σ a_k \|b_k⟩ | U_j = Be[A_j/λ_j]、B_k\|0⟩ = \|b_k⟩、K ≥ ‖A^{-1}‖、0 < R_0 ≤ ‖A^{-1}b‖ | C_j、c_k | Σ C_j Q_j = O((K⟨C,λ⟩_{1/2} + ‖C‖_1) log(1/ε))、Σ c_k Q_{b,k} = O((K/R_0)⟨c,\|a\|⟩_{1/2} + ‖c‖_1)；単一: Q_H = O(κ log(1/ε))、Q_b = O(p^{-1/2})；因子: Q_T = O(√κ p^{-1/4} + √κ log(1/ε)) | Thm 6.7, 6.8, Cor 6.9 |
| 6.3.4 | 古典証明書つき QLSP | 同上 | 解の尾部 ‖1_{[0,1/K)}(\|A\|)x‖ ≤ cεr_0、または有限 query の逆近似 | — | Q_A = O(K log(1/ε))、Q_b = O(K/r_0)；または Q_A = O(d_A β/y_0)、Q_b = O(1 + β/y_0) | Thm 6.10, Cor 6.11, Lemma D.9, Prop D.12, D.13 |
| 6.4 | 線形微分方程式 | x' = −H(t)x + b(t) の正規化終状態 | Be[H(t)/α]（時刻制御）、x_0 と b(t)/β の準備；‖U(t,s)‖ ≤ C、sup‖x‖ ≤ g、‖x(T)‖ ≥ r | C_ℓ、c_k | Q_H = O((C m W_2/r) log(1/ε))、Q_0 + Q_b = O(CB/r)（m = Θ(αT)）；多 oracle 版 (6.210)–(6.211) | Thm 6.12–6.19 |
| 6.5 | 一般化固有値推定 | Aψ = λBψ の λ | Be[A/α_A]、Be[B/α_B]、U_ψ；βI ⪯ B ⪯ b_max I、spec(B^{-1/2}AB^{-1/2}) ⊆ [−R,R] | C_A、C_B、C_ψ | Q_A = O((α_A/(βε)) log(1/δ))、Q_B = O((Rα_B/(βε)) log(1/δ))、Q_ψ = O(√κ_B log(1/δ)) | Thm 6.20, 6.21, Prop D.19 |
| 6.6 | 基底状態準備とエネルギー推定 | \|g⟩ の準備、E_0 の推定 | Be[H/λ]（self-inverse）、B\|0⟩ = \|ψ⟩、\|⟨g\|ψ⟩\|^2 ≥ p_0；閾値 u < v（角度差 d）または gap γ_0（角度 d_*） | q_H、q_B | 閾値: q_B = O(p_0^{-1/2})、q_H = O(d^{-1}[p_0^{-1/2} + log(1/ε)])；gap: q_B = O(p_0^{-1/2} log(1/ε))、q_H = O(d_*^{-1} p_0^{-1/2} log(1/ε))；gap なしエネルギー: q_H = O(λ/(ε_E √p_0) log(1/q)) | Thm 6.22, Prop 6.23, 6.24 |

番号付き主張の数: §6 に 24 個（Thm 6.1–6.5, Lemma 6.6, Thm 6.7, 6.8, Cor 6.9, Thm 6.10, Cor 6.11, Thm 6.12–6.16,
Prop 6.17, Thm 6.18, Cor 6.19, Thm 6.20–6.22, Prop 6.23, 6.24）、付録 C に 3 個（Lemma C.1, Prop C.2, C.3）、
付録 D に 19 個（D.1–D.19）、合計 46 個。これに加えて、再利用価値が高い番号なしの主張 29 個を §3.4 に挙げる。

## 2. 組み立てレシピ

各項目は (a) ネットワーク式、(b) 新規・特化 module（system matrix と transfer function）、(c) 解析データ
（群遅延 W、a, w, h±, ζ, M_loc、radial exponent A±）、(d) 使う clock・compilation 定理、(e) query 数、
(f) 形式化上の注意、の順に書く。

### 2.1 §6.1.1 重み付き Hamiltonian simulation（Thm 6.1）

- (a) ネットワーク:
  `F = Substitute(Exp_{tΛ}; port := WeightedCayley(E; V_1,…,V_m))`、`G(z) = F(z^{r_1},…,z^{r_m})`（`Delay_r`）、
  `A = Attn(1/(a(1+δ))) ∘ Compile_N[X_sine](G)`。Exp は有限実現 `ExpFin_{tΛ,R}`（Thm 5.6）に置き換える（6.1.4）。
- (b) module（新規なし。WeightedCayley は Lemma 5.2 で C = E†, K0 = 0 とした場合）:
  - E = (√(λ_1/Λ)(⟨0|_1⊗I), …, √(λ_m/Λ)(⟨0|_m⊗I)) : ⊕_j K_j → H_sys、EE† = I、Π = E†E（(6.6)）。K_j は V_j の全 Hilbert 空間。
  - S_Cayley = [[0, −iE], [E†, i(I−Π)]]（公開/私的の順）、Ô(z) = ⊕_j z_j V_j（(6.7)）。
  - C(z) = −iE Ô(z)[I − i(I−Π)Ô(z)]^{-1} E† = (I − M(z)/Λ)(I + M(z)/Λ)^{-1}（(6.8)）、
    M(z) = Σ_j λ_j [(1−z_j^2)/(1+z_j^2) I + i·2z_j/(1+z_j^2) H_j]（(6.9)）。鍵は V_j^2 = I から
    (I + i z_j V_j)(I − i z_j V_j)^{-1} = [(1−z_j^2)I + 2i z_j V_j]/(1+z_j^2)。M は polydisk で accretive。
  - F(z) = Exp_{tΛ}(C(z)) = e^{−tM(z)}、F(1) = e^{−itH}（(6.10)）。有限 Exp と融合した system (6.11):
    S = [[A_Exp⊗I, −iB_Exp⊗E], [C_Exp⊗E†, iI_D⊗(I−Π) − iD_Exp⊗Π]]、Ô_Exp(z) = I_D ⊗ ⊕_j z_j V_j。
    選択部分は S_Exp diag(1, −iI_D)、補空間は iI なので unitary。Exp の mode label は oracle 呼び出しで不変。
- (c) 解析データ:
  - M(1) = iH、∂_{z_j}M(1) = −λ_j I（スカラー）。Thm 2.1 から F†∂_{z_j}F = tλ_j I（(6.12)）。
    遅延込みの群遅延は W = Ω I、Ω = t Σ_j λ_j r_j（(6.13)）。すなわち a = w = Ω。
  - |log z| ≤ s、s r_j ≤ u ≤ 1/2 で ‖G(z)‖ ≤ |z|^{A−}（|z| ≤ 1）、|z|^{A+}（|z| ≥ 1）、
    A± = t Σ_j λ_j r_j / (1 ∓ sin(s r_j))（(6.15)）。証明は (C.1)–(C.2) の Hermitian 部評価と
    ‖e^T‖ ≤ exp(λ_max((T+T†)/2))。項の同時対角化は不要。M_loc = 1。
- (d) clock: Lemma 3.6（smoothed flat window）を sine clock（C.1.1, (C.3)–(C.8)）で特殊化。
  g_±(rL_0 + s) = (±1)^r L_0^{-1/2} √(2/(K+1)) sin((r+1)θ)、θ = π/(K+1)、a = cos θ。
  signed correlation W(n) は |n| ≤ L_0 で 1、非負・対称・単調、全変動 2。Thm 2.3 により label は高々 6 個。
  horizon は N ≤ Ω + ((K + sin u)/cos^2 u) s t Σ_j λ_j r_j^2 + O((K/s) log(1/(aε)))（(6.16)/(C.7)）。
  K = Θ(δ^{-1/2})（(C.14)）で a ≥ 1/(1+δ)。最後に Attn で正規化を 1+δ に合わせる。
- 遅延配分: 連続最適は r_j ∝ √(C_j/λ_j)（(6.14)、Lemma 3.12 の p = 1）。二次モーメントを残したまま
  clip と丸めを行う不等式 (C.9)–(C.16)（x_j = min{u, η√(C_j/μ_j)}、r_j = ⌈P x_j⌉）。
- (e) query: q_j = ⌊(N−1)/r_j⌋（(6.4)）、Σ_j C_j q_j ≤ (1+δ) t⟨C,λ⟩_{1/2} + O(δ^{-2}‖C‖_1 log(1/ε))（(6.5)）。
  定数は項数・Hamiltonian・強度・コストに依存しない。成功確率は全入力で ≥ (1−ε)^2/(1+δ)^2。
- 有限 Exp: C_r(0) = 0 なので X = T_N[C_r] は縮小かつ X^{⌈N/r_min⌉} = 0。Thm 5.6 のスペクトル実現
  （τ = tΛ）の誤差は τ^3 K(K−1)(2K−1)/(9π^4 R^3)、K = ⌈N/r_min⌉（(6.50)）。代替は Schur-prefix 実現（誤差 0）
  または Cor B.5 の Padé 近似（付録 B）。
- (f) 注意: 「z=1 での恒等式と群遅延（代数）」と「radial exponent と sine clock（解析）」に分けて形式化できる。
  前者は ∂_jM(1) がスカラーなので行列指数の微分が自明になり、難度が低い。

### 2.2 §6.1.2 SOS phase amplification（Thm 6.2）

- 問題設定: H = Σ_j A_j†A_j を公開空間 X 上に与える（長方形 factor も可）。λ_j(⟨0|_j⊗I)V_j†Π_out,j V_j(|0⟩_j⊗I) = A_j†A_j（(6.19)）。
  P_j = V_j†Π_out,j V_j、R_j = 2P_j − I = V_j†(2Π_out,j − I)V_j（(6.20)、ReflectionWalk 型の信号 (5.13)）。
  1 回の feedback 演算は各方向に 1 回ずつ factor oracle を呼ぶ。
- 目標: 拡大公開空間 P = X ⊕ ⊕_j K_j 上の bipartite Hermitian dilation ℋ = [[0,B†],[B,0]]、
  B = (√ω_j P_j(|0⟩_j⊗I))_j、ω_j = λ_j/Λ、B†B = H/Λ（(6.21)）。U = (I − iρℋ)^J (I + iρℋ)^{-J}（(6.23)）、
  J = kJ0、ρ = 1/J0。正エネルギーの不変平面 (6.22) 上で ℋ = √(E/Λ) X、位相は
  ±φ_k(E)、φ_k(E) = 2kJ0 arctan(√(E/Λ)/J0) = 2k√(E/Λ) + O(kρ^2 (E/Λ)^{3/2})（(6.17)–(6.18)、(C.18)）。
- (a) ネットワーク: `G = Delay_r(Series^{J}(ProjectorCayley_ρ))`、`A = Attn ∘ Compile_N[X_flat](G)`。
  有限有理 target なので Exp 近似は不要。
- (b) ★ ProjectorCayley_ρ（Lemma 5.2 の特殊例だが、結合が遅延に依存する点が新しい）:
  - 分解 P_j = (I + R_j)/2 により ℋ = H_0 + Σ_j H_j、H_0 は既知で ‖H_0‖ = ‖Σ_j H_j‖ = 1/2（(6.28)）。
  - port j の私的空間は C^2 ⊗ K_j、O_j = X_dir ⊗ R_j（(6.29a)）。結合
    E_j(ξ ⊕ δ) = √(ω_j r_j/(2D_r)) (⟨0|_j⊗I)ξ ⊕_j √(D_r/(2r_j)) δ、K_j = E_jE_j†、D_r = (Σ_j ω_j r_j^2)^{1/2}（(6.29b)）。
    E_jO_jE_j† = H_j、−K_j ⪯ H_j ⪯ K_j、Σ_j r_j K_j = (D_r/2) I_P（(6.30)）。
  - load M(z) = iH_0 + Σ_j [(1−z_j^2)/(1+z_j^2) K_j + i 2z_j/(1+z_j^2) H_j]、F_ρ(z) = (I − ρM(z))(I + ρM(z))^{-1}、M(1) = iℋ（(6.31)）。
  - system S_ρ = [[2L_ρ − I, −2i√ρ L_ρE], [2√ρ E†L_ρ, i(I − 2ρE†L_ρE)]]、L_ρ = (I + ρEE† + iρH_0)^{-1}（(6.32)）。
    Lemma 5.2 で C = √ρE†、K0 = ρH_0。unitarity は L + L† = 2L†(I + ρEE†)L（(C.20)）。
  - J 段直列: F(z) = F_ρ(z)^J、IJ ⊗ Ô(z)（(6.33)）。全ブロックは (B.38)。
- (c) 解析データ: 遅延込み catalyst U†G' = kD_r(I + ρ^2ℋ^2)^{-1}（(6.34)、評価値と可換なので J 段で加算）。
  Lemma C.1: 半径 1 − e^{−u/r_*} = Θ(u/r_*)、A± = kD_r[1 ± (3ρ^2 + 5u)]。
- (d) clock: Thm 3.9 の two-sided 形 (C.27): N ≤ KA_+ − (K−1)A_− + O(Kζ^{-1} log(16/ξ))。
  パラメータ (C.28): K = ⌈π/√δ⌉、J0 = ⌈√(128K/δ)⌉ = Θ(δ^{-3/4})、u = δ/(256K)、a = cos(π/(2K))。
  N ≤ (1 + 11δ/128) kD_r + O(δ^{-2} r_* log(16/ξ))（(C.29)、(6.35)）。
- 遅延配分: Lemma 3.12 の p = 2。inf_{r_j>0} D_r Σ_j c_j/r_j = Λ^{-1/2}(Σ_j c_j^{2/3} λ_j^{1/3})^{3/2}、r_j ∝ (c_j/ω_j)^{1/3}（(6.36)）。
  clip と丸めは (C.31)–(C.33)、この段で δ^{-3} が出る。
- (e) query: Q_{V_j} = Q_{V_j†} = q_j = ⌊(N−1)/r_j⌋（(6.26)）、
  Σ_j c_j q_j ≤ (1+δ)(k/√Λ)(Σ_j c_j^{2/3}λ_j^{1/3})^{3/2} + O(δ^{-3}‖c‖_1 log(1/ε))（(6.27)）。
  エネルギー感度版 (6.38): t_eq = k/√(ΛΓ(1 + ρ^2Γ/Λ)) で (1+δ) t_eq √Γ (Σ_j c_j^{2/3}λ_j^{1/3})^{3/2} + …。
- 比較: 厳密 reflection walk W = −(2JJ† − I)R、J†W^kJ = T_k(I − 2H/Λ)（(6.39)/(C.34)）、コスト k‖c‖_1。
  Prop C.2: エネルギーだけで決まる厳密な位相対を作るには q_j ≥ ⌈k⌉。gate は Lemma B.3 + Thm A.5（(6.40)–(6.42)）。
- (f) 注意: module の system matrix が遅延スケジュール r に依存する。言語では「遅延を module 構成後に付ける」
  だけでは足りない（§6 の F1 参照）。

### 2.3 §6.1.3 共有 SELECT（Thm 6.3）

- 設定: V_j = P_j† SEL P_j（(6.43)）、SEL = SEL† = SEL^{-1} はコスト C_S、c_j = C_{P_j} + C_{P_j†} ≥ 0。
- (a) transfer function は 6.1.1 と同一（`Exp_{tΛ} ∘ WeightedCayley`）。変わるのは feedback 演算の実現だけ。
- (b) ★ batched feedback 実現: tick k > 0 で D_k = {j : r_j が k を割り切る}。
  P_k† SEL_{D_k} P_k = ⊕_{j∈D_k} V_j ⊕ I、P_k = ⊕_{j∈D_k} P_j ⊕ I（(6.44)）。SEL は D_k の合併上で 1 回。
- (c)(d) 6.1.1 と同じ解析。固定遅延 clock（正規化 1+ν、誤差 min{ε/16, ν}）で
  N ≤ (1+ν) t Σ_j λ_j r_j + O(ν^{-2} r_* log(16/min{ε,ν}))（(6.47)）。
- 遅延: r̄_j = max{1, ⌈√(Λc_j/(C_Sλ_j))⌉}（(6.48)）。丸め不等式 (Σ_j λ_j r̄_j)(C_S + Σ_j c_j/r̄_j) < 2D_0、
  D_0 = (√(ΛC_S) + Σ_j √(λ_j c_j))^2（(6.49)、(C.38)–(C.39)）。余裕 γ = 1 − L_0/(2D_0) ∈ (0,1]、
  ν = min{δ, (2D_0 − L_0)/(2L_0)}（(C.40)–(C.41)）。
- (e) query: Q_{P_j} = Q_{P_j†} = ⌊(N−1)/r_j⌋、q_S = |∪_j {r_j, 2r_j, …} ∩ {1,…,N−1}| ≤ N−1（(6.45)）、
  C_S q_S + Σ_j c_j q_j ≤ (2−γ) t D_0 + O_{λ,c,C_S,δ}(log(1/ε))（(6.46)）。一様な δ 依存を持つ別形は
  2(1+δ) t D_0 + O(δ^{-2} r̄_*(C_S + Σ_j c_j) log(1/ε))（(C.43)）。
- (f) 注意: transfer function は変わらず、コストモデル（共有 sub-oracle を tick ごとに 1 回数える）だけが変わる。
  SEL が self-inverse でない場合は SEL と SEL† の両方を数える必要がある。

### 2.4 §6.1.5 sparse Hamiltonian simulation（Thm 6.4）

- oracle: O_f|x,ℓ⟩ = |x, f_x(ℓ)⟩（最初の d 個が行の support、残りは異なるゼロ位置で埋める in-place 置換）、
  O_H は (x,y) に H_xy を書く。両方とも controlled と inverse を使える。
- (a) ネットワーク: `F_v = Substitute(Exp_{tv}; port := Sparse2(U_v))`、
  `A = Compile_N[analytic, 正規化 2](F_v)`（有限 Exp に置換）、その後 `OAA`（Lemma A.4）で A_sim。
- (b) ★ edge rotation（query group）と ★ Sparse2 junction:
  - A_v = (d/v) Σ_{x,y} H_xy |x,y⟩⟨y,x|、T_v = P_d† O_f† A_v O_f P_d、U_v = (I − iT_v)(I + iT_v)^{-1}（(6.57)）。
    P_d|0⟩_j = d^{-1/2} Σ_{ℓ<d} |ℓ⟩_j。基底 (|x,y⟩, |y,x⟩) での edge rotation は
    [[cos ϑ, −ie^{iϕ} sin ϑ], [−ie^{−iϕ} sin ϑ, cos ϑ]]、ϑ = 2 arctan|a|、ϕ = arg a、a = dH_xy/v（(6.58)）。
    回路 (6.59): アドレスの可逆ソート → O_H → 回転 → O_H† → 逆ソート、全体を O_f P_d で共役。
    1 query group = O_f、O_H、O_H†、O_f† 各 1 回。
  - Sparse2: Π_j = I ⊗ |0⟩⟨0|_j、S_0 = [[0, I⊗⟨0|_j], [I⊗|0⟩_j, −(I − Π_j)]]、Ô_v(z) = zU_v（(6.62)）。
    M_v(z) = v⟨0|_j (I − zU_v)(I + zU_v)^{-1} |0⟩_j、C_v = (I − M_v/v)(I + M_v/v)^{-1}、C_v(0) = 0、
    F_v(z) = Exp_{tv}(C_v(z)) = e^{−tM_v(z)}、F_v(1) = e^{−itH}（(6.63)）。(I − U_v)(I + U_v)^{-1} = iT_v なので M_v(1) = iH。
    融合 system (6.69)。
- (c) 解析データ: ⟨0|_j T_v |0⟩_j = H/v、D_2 = ⟨0|_j T_v^2 |0⟩_j = (d/v^2) diag_x Σ_y |H_xy|^2 ⪯ I（v ≥ √d s_2 のとき）、
  ‖T_v‖ ≤ d h_max/v（(6.60)–(6.61)）。Re M_v ⪰ 0（円板内、(6.64)）。(I + U_v)^{-1} = (I + iT_v)/2 から
  −M_v'(1) = v(I + D_2)/2、F_v†F_v'(1) = (tv/2)∫_0^1 e^{iutH}(I + D_2)e^{−iutH} du、(tv/2)I ⪯ … ⪯ tv I（(6.65)、H と D_2 は非可換でよい）。
  ζ = 1/(64(1 + max{1, d h_max/v}))（(6.66)）、|z| ≥ 1 で ‖F_v(z)‖ ≤ |z|^{2tv}（(6.68)）。
  Cor 3.10 に a = tv/2、w = tv、h_− = tv/2、h_+ = tv、M_loc = 1 を入れる。
- (d) clock: Cor 3.10（正規化 2）。有限 Exp: Thm 5.6 と (6.50)（τ = tv、r_min = 1、T_N[C_v]^N = 0）。
  Prop 3.17 が有限変換の誤差を因子 2 で encoded operator に移す。
- (e) query: O_f、O_f†、O_H、O_H† をそれぞれ N−1 回、Q_f = Q_H = 2(N−1)、N = O(tv + 1 + (d h_max/v) log(1/ε))（(6.54)）。
  v = max{√d s_2, √(d h_max log(1/ε)/t)}（(6.70)）で O(t√d s_2 + √(t d h_max log(1/ε)) + log(1/ε))（(6.55)）。
  OAA（Lemma A.4）で query は 3 倍、‖A_sim(|0⟩_a⊗I) − |0⟩_a⊗e^{−itH}‖ ≤ ε（(6.56)）。
- (f) 注意: Boolean oracle と可逆算術（ソート・固定小数点の角度計算）のモデルが必要。
  「power を compression より先に取る」second moment の計算 (6.60) が解析の核。

### 2.5 §6.2 重み付き coherent state summation（Thm 6.5, Lemma 6.6）

- 設定: U_j|0⟩ = λ_j|0⟩_f|ψ_j⟩ + b_bad,j、λ_j ∈ [λ_0j, 1]、コスト C_j（U_j、U_j† とも）。A = Σ_j |a_j|、
  s = ‖Σ_j a_j|ψ_j⟩‖ ≥ s_0、|Ψ⟩ = Σ_j a_j|ψ_j⟩/s（(6.71)–(6.72)）。
- (a) ネットワーク（4 層を substitution で 1 つの transfer function にまとめ、clock は 1 回だけ）:
  `Branch_j = Sign_{L_j}(BranchHerm(PrepQuery(U_j)))`、
  `F_± = Substitute(WeightedCayley_E; port j := ∓i σ_x ⊗ Branch_j)`、
  `Loader_± = Series^{J}(SmallStepCayley_{τ/J,±})`（または直接 F_±）、
  `𝔽(z) = V_D F_{σ_D}(z) V_{D−1} ⋯ V_1 F_{σ_1}(z) V_0`（(6.92)、σ_k ∈ {+,−}、F_− は Inverse 規則による逆方向 loader）、
  `b = Project(Compile_N[analytic, 正規化 2](Delay_r(𝔽)))`。
- (b) module:
  - ★ BranchHerm: K_j = λ_j(|out,ψ_j⟩⟨in| + |in⟩⟨out,ψ_j|)、H_j = (K_j + (λ_0j/2)I)/(1 + λ_0j/2)（(6.76)）。
    既知の入出力射影、Hermitian block encoding 構成、恒等との LCU から U_j, U_j† 定数回で involutory Be[H_j]。
    |spec H_j| ≥ λ_0j/(2 + λ_0j)、sgn(H_j)|in⟩ = |out,ψ_j⟩（(6.77)）。入出力平面上は λ_jσ_x で、shift により kernel も gap を持つ。
  - Sign path（(B.6)、Lemma B.1、alternating-reflection purifier [BJ26]）: S_sign,j = [[0, ι_j†], [ι_j, I − ι_jι_j†]]、
    P_j(z_j) = z_j ι_j† W_j [I − z_j(I − ι_jι_j†)W_j]^{-1} ι_j（(6.78)）、L_j = O(λ_0j^{-1} log(2/η)) で誤差 η。
  - WeightedCayley（isometry 形）: J_j|s⟩ = e^{i arg a_j}|0⟩|e⟩、J_j|v⟩ = |1⟩|v⟩、E = ⊕_j √(|a_j|/A) J_j、E†E = I（(6.79)）。
    R_j = σ_x ⊗ P_j、M_±(z) = Σ_j (|a_j|/A) J_j†(I ± iR_j)(I ∓ iR_j)^{-1}J_j、F_± = (I − M_±)(I + M_±)^{-1}（(6.80)）、
    S = [[0, E†], [E, −I + EE†]]（(6.81)）。z=1 で F_− = F_+†。
    理想極限で star Hamiltonian ℋ = (1/A)[[0, Σ_j a_j⟨ψ_j|], [Σ_j a_j|ψ_j⟩, 0]]（(6.82)）、
    F_+|s⟩ = [(1 − (s/A)^2)|s⟩ − 2i(s/A)|Ψ⟩]/(1 + (s/A)^2)（(6.83)）。
  - ★ SmallStepCayley: C_{Δ,±}(z) = [I − (Δ/2)M_±][I + (Δ/2)M_±]^{-1}、U_{τ,J,±} = C_{τ/J,±}^J → e^{−τM_±}（(6.84)）、
    system S_Δ（(6.85)、公開空間と結合像の上で 2 mode 反射、残りは −I）。
    e^{−iτℋ}|s⟩ = cos(τs/A)|s⟩ − i sin(τs/A)|Ψ⟩（(6.86)）。誤差 ‖U_{τ,J,±} − e^{∓iτℋ̃}‖ ≤ τ^3/(12J^2)、
    ‖e^{∓iτℋ̃} − e^{∓iτℋ}‖ ≤ τη（(C.52)）。
  - ★ loader と位相付き Grover 段: B_+ = Z_gU_{τ,J,+}、B_− = U_{τ,J,−}Z_g†、Z_g = Π_s + iΠ_g（(6.88)）、
    Q_{ϕ,θ}(z) = B_+(z)R_s(ϕ)B_−(z)R_g(θ)（(6.90)）、B_+R_s(ϕ)B_− = I + (e^{iϕ} − 1)B_+|s⟩⟨s|B_+†（(C.53)）。
  - 外側の振幅増幅: s 未知なら実奇数の singular-value filter [GSLW19] で次数 D = O((A/s_0) log(1/ε))（(6.91)）、
    s 既知なら厳密 AA [BHMT02] で D = O(A/s)、または τ = πA/(2s) で D = 1。
- (c) 解析データ（Lemma 6.6）: G = 𝔽(z^{r_1},…) は円板で縮小、z=1 で unitary、
  |z − 1| ≤ c(max_j r_j/λ_0j)^{-1} で解析、|z| ≥ 1 で log‖G(z)‖ ≤ c'(D/A) Σ_j |a_j| r_j/λ_0j log|z|（(6.93)–(6.94)）。
  証明は (C.44)（‖P_j(z_j) − P_j‖ ≤ C|z_j − 1|/λ_0j、‖∂P_j‖ ≤ C/λ_0j）、(C.45)–(C.47)。HamSim ルートは D を Dτ に置換（(C.54)–(C.56)）。
- (d) clock: Cor 3.10（正規化 2、a = h_− = 0）。N = O((D/A) Σ_j |a_j| r_j/λ_0j + max_j (r_j/λ_0j) log(1/ε))（(6.95)）、
  HamSim ルートは (6.96)。
- 遅延: 率 t_j = (log(2/ε))/λ_0j + (D/A)√(|a_j|/(λ_0jC_j)) Σ_k √(|a_k|C_k/λ_0k)、r_j = ⌈T/t_j⌉（(C.58)–(C.59)）。
  連続最適は Lemma 3.12 の p = 1（(6.97)）。
- (e) query: (6.74)/(6.75)（§1 の表）。‖b − |Ψ⟩/2‖ ≤ ε/4（(6.73)）、p_succ ∈ [(1/2 − ε/4)^2, (1/2 + ε/4)^2]、
  条件付きベクトル誤差 ≤ ε（(C.61)）。誤差配分 η ≤ ε/(128D)（(C.57)）。
- (f) 注意: 中間で postselection も clock 正規化の積も起こらない。ただし outer FPAA の多項式は QSVT 側の結果
  （位相保存 odd sign 近似）に依存する。Cor 5.8（StatePrep）は Thm 6.1 を通る別ルート。

### 2.6 §6.3.1 単一行列 QLSP: nullspace reflection と scale cascade（Thm 6.7 / Cor 6.9 の 1 行列版）

- 拘束: A_ρ = (H, −|b⟩/ρ)、ker A_ρ = span{(H^{-1}|b⟩/ρ, 1)}（(6.113)）。公開空間 H ⊕ C、スカラー座標を初期化し、出力は H 側を選ぶ。
- (a) ネットワーク:
  `CJ_ρ = Close_Y(I)( CJ(K0 = 0; C_H, C_b; V_H, V_b) )`、
  `Casc = Series_{scalar port}(CJ_{ρ_J}, …, CJ_{ρ_0})`（各段の system 出力は直交する scale sector に残す）、
  `(y^{N0}, e^{N0}) = Compile_{N0}[uniform](Delay_{(r_H=1, s=⌈r_0⌉)}(Casc))`（公開出力と末端私的出力の両方を使う）、
  `out = RowSelect(v^{N0}, −iβ J_H (L/ℓ) e^{N0}) / √(1+β^2)`、`J_H = WeightedReciprocal(H)`（Lemma D.2）。
- (b) ★ ConstraintJunction（wave-digital scattering junction [Fet86]）:
  - load K_ρ = κ[[0, 0, H], [0, 0, −⟨b|/ρ], [H, −|b⟩/ρ, 0]]、座標 (x, c, y)、Y ≃ H は閉じる（(6.119)）。スカラー版は (6.116)–(6.118)。
  - 結合 C_H(x,c,y) = √κ((|0⟩⊗I)x, (|0⟩⊗I)y)、V_H = [[0, O_H], [O_H, 0]]（(6.122)）、
    C_b(x,c,y) = √(κ/ρ)((|0⟩_w⊗I)y, c|0⟩)、V_b = −[[0, B], [B†, 0]] = −PrepQuery(B)（(6.123)）。
  - R = (I + C†C)^{-1}、C†C = diag(κI, κ/ρ, (κ + κ/ρ)I)（(6.125)、既知スカラーの逆だけ）、
    S_0 = [[2R − I, 2RC†], [2CR, 2CRC† − I]]、Ô(z) = (−iz_H V_H) ⊕ (−iz_b V_b)（(6.124)）。
  - Y の恒等閉包: S_ρ = S_ee + S_eY(I − S_YY)^{-1}S_Ye（(D.2)）（多 oracle 版では (S_0)_YY = 2(1 + K‖λ‖_1 + K‖a‖_1/ρ)^{-1}I − I）。
  - z=1: F_ρ(1) = 2Π_{ker A_ρ} − I（(6.120)、平均波が ker A_ρ、差の波が ran A_ρ† = (ker A_ρ)^⊥）。
    F_ρ(1)(0,1) = (2H^{-1}|b⟩/(ρ(1 + r^2/ρ^2)), (1 − r^2/ρ^2)/(1 + r^2/ρ^2))、r = ‖H^{-1}|b⟩‖（(6.121)）。
    定常値 c = 1/(1 + r^2/ρ^2)、x = (c/ρ)H^{-1}|b⟩、y = (i/κ)H^{-1}x（(6.128)）。
  - ★ scale cascade（impedance matching）: r_0 = κ√p、D = κ/r_0、ρ_j = 2^j r_0、j = ⌈log2 D⌉, …, 0（(6.126)）。
    r/ρ_j ∈ [1/2, 1] となる段で透過 [2(r/ρ_j)/(1 + (r/ρ_j)^2)]^2 ≥ 16/25（(6.127)）、総定常透過も ≥ 16/25。
- (c) 解析データ（energy identity = Thm 2.1）: feedback j の二乗振幅は 2‖C_j h‖^2。W_H ≤ κ、W_b < 4D（(6.129)）。
  遅延込み W ≤ W_H + sW_b < 9κ。
- (d) compilation: 一様 clock（Thm 3.2、Lemma D.1）で N_0 = O(κ)。有限恒等式（(6.130)–(6.131)）:
  Hv^{N0,ρ} = (2c^{N0,ρ}/ρ)|b⟩ + (2i/(κ√N_0)) L_{ρ,s} e^{N0,ρ}、L_{ρ,s}L_{ρ,s}† = (κ/2)(1 + s/ρ)I。
  末端写像 L_{ρ,s} は既知の座標演算と O(1) 回の oracle で実装（Lemma D.1）。
- 精度補正: ‖J_H − H^{-1}/(4κ)‖ ≤ η の行列のみ block（Lemma D.2、O(κ log(1/ε)) 回の行列 query、準備 query なし）。
  既知の行選択 (v^{N0} − iβJ_H(L/ℓ)e^{N0})/√(1 + β^2)、β = 8ℓ/√N_0（(6.132)）。厳密逆なら各 scale 成分が H^{-1}|b⟩ に比例。
- (e) query: Q_H = O(κ log(1/ε))、Q_b = O(D) = O(p^{-1/2})（Cor 6.9）。
- (f) 注意: 有限 lift の**末端私的振幅**を後段のデータとして使う点が、transfer function at z=1 の意味論を超える（§6 の F7）。

### 2.7 §6.3.2 Hermitian factor（Thm 6.8、Cor 6.9 の因子版）

- H = T^2。スカラー設計では拘束を 2 本の一次関係 √κ xξ = √D u、√(κD) xu = (κ/ρ)c に分ける（(6.133)）。
- ★ factor-chain load K_ρ^fac（(6.134)、5 座標 (ξ, c | y1, u, y2)、中央 3 座標は閉じる）。閉じた行は
  u = √r_0 xξ、y1 = √κ x y2、x^2 ξ = c/ρ（(6.135)）、公開 transfer は x^2 を持つ反射（(6.136)）。
  多項版の結合 C_{j,1} = √(√κ λ_j)(…)、C_{j,2} = √(√(κD) λ_j)(…)、D_k、K0 = −√D(|y1⟩⟨u| + |u⟩⟨y1|) ⊗ I（(D.21)–(D.22)）、
  Gram 行列 (D.24)。2 本の信号辺は oracle 空間の別コピーにあり、1 回の制御 O_T 呼び出しが両方に作用する。
- 定常: u = √r_0 Tx、y1 = (i/√κ)T^{-1}x、y2 = (i/κ)T^{-2}x（(6.137)/(D.25)）、すべて ≤ ‖x‖（(D.26)）。
  重み W_T ≤ √κ + √(κD)、W_b < 4D（(6.138)/(D.27)）。
- 残差: Hv^{N,ρ} = (2c/ρ)b + (2i/(κ√N))(L_{2,ρ} + √κ T L_{1,ρ})e^{N,ρ}（(6.139)/(D.29)）、Gram (D.30)。
- 補正: Lemma D.2 を逆ノルム √κ で T に適用して J ≈ T^{-1}/(4√κ)。別々の成功 ancilla で 2 回実行して
  ‖J^2 − T^{-2}/(16κ)‖ ≤ 2η（(D.33)）。行選択 (D.34)、β_1 = 8ℓ_1/√N_0、β_2 = 32ℓ_2/√N_0、N_0 = ⌈2^16 L⌉。
- 率: (D.31)（coarse）、(D.36)（reciprocal 用の独立な遅延）。Q_{T,j} = O(t_j + v_j log(1/ε))、Q_{b,k} = O(u_k)（(D.37)）。

### 2.8 §6.3.3 多 oracle QLSP（Thm 6.7）

- load K_ρ = K[[0, 0, H], [0, 0, −b†/ρ], [H, −b/ρ, 0]]、H = Σ_j H_j、b = Σ_k a_k|b_k⟩（(6.141)）。
- 結合 C_j(x,c,y) = √(Kλ_j)((|0⟩_j⊗I)x, (|0⟩_j⊗I)y)、V_j = [[0, O_j], [O_j, 0]]（(6.142)）、
  D_k(x,c,y) = √(K|a_k|/ρ)((|0⟩_{w_k}⊗I)y, c|0⟩)、W_k = −[[0, (a_k/|a_k|)B_k], [(a_k*/|a_k|)B_k†, 0]]（(6.143)、self-inverse）。
  Gram C†C = diag(K‖λ‖_1 I, K‖a‖_1/ρ, K(‖λ‖_1 + ‖a‖_1/ρ)I)（(6.144)）。準備写像の codomain は直交するので |b_k⟩ 間の重なりは Gram に現れない。
- scale: ρ_j = 2^j R_0、j = ⌈log2(K‖a‖_1/R_0)⌉, …, 0（(6.145)）。重み W_j ≤ Kλ_j、W_{b,k} < 4K|a_k|/R_0（(6.146)–(6.147)）。
- 残差: Hv^{N0,ρ} = (2c/ρ)b + (2i/(K√N_0))L_ρ e^{N0,ρ}、L_ρL_ρ† = (K/2)(Σ_j λ_j r_j + (1/ρ)Σ_k |a_k| s_k)I（(6.148)–(6.149)）。
- 率と遅延: t_j = 1 + K√(λ_j/C_j) Σ_i √(C_iλ_i)、u_k = 1 + (K/R_0)√(|a_k|/c_k) Σ_l √(c_l|a_l|)（(6.150)）、
  r_j = ⌈L/t_j⌉、s_k = ⌈L/u_k⌉、L ≥ max{1, t_j, u_k}（(6.151)）。KΣλ_jr_j ≤ 2L、(K/R_0)Σ|a_k|s_k ≤ 2L（(6.153)）。
  coarse の遅延込み重み ≤ 10L、末端写像の二乗ノルム ≤ 2L、N_0 = O(L)（Prop D.3 では ⌈4096L⌉）。
  reciprocal は同じ行列遅延で N_1 = O(L log(1/ε))（(6.154)）。
- query: Q_j = O(t_j log(1/ε))、Q_{b,k} = O(u_k)（(6.155)）。C_j、c_k を掛けて和を取ると (6.104)–(6.105)。
  scale 系と reciprocal 節に現れる同一 oracle の出現は direct sum を占め、予定 tick で 1 回の制御呼び出しが全体に作用する。
- 非 Hermitian A_j: termwise dilation H_j = [[0, A_j], [A_j†, 0]]、O_j = [[0, U_j], [U_j†, 0]]（(6.156)–(6.157)）。K、R_0 は不変。

### 2.9 §6.3.4 古典証明書（Thm 6.10, Cor 6.11, 付録 D.3–D.5 節）

- 同じ拘束回路を証明書から選んだ K で走らせる（回路は変えない）。解析だけが変わる:
  x を特異値閾値で分割（(D.50)）、b_≥ を準備する比較 oracle B_≥ を ‖B_≥ − B‖ ≤ √2 t_b で取り（(D.53)）、
  hybrid 誤差は準備呼び出し数にのみ比例（(6.166)/(D.54)）。support 上の不変空間は Lemma D.8/D.9。
- 証明書の種類: 大域逆ノルム、逆モーメント µ_q ≥ ‖|A|^{-q}x‖ ⇒ τ(K) ≤ µ_q/K^q（(6.170)/(D.64)）、
  sector 分解 (6.172)/(D.72)、特異値帯 (6.173)/(D.73)、正モーメント m_j = ⟨b|(AA†)^j|b⟩ と多項式 majorant（(6.174)/(D.77)–(D.78)）。
- 別ルート: 入力特化の有限 query 逆近似 F = A†p(AA†)（(6.175)）を bounded-budget AA で増幅（Prop D.12、Lemma D.10）。
  annihilating 多項式 (6.177)/Prop D.13、冪の LCU（Lemma D.18）。
- 多 oracle 版の support 制限には共通不変条件 A_jP_R = P_LA_j、P_L|b_k⟩ = |b_k⟩（(6.178)）が必要。

### 2.10 §6.4 線形微分方程式（Thm 6.12–6.19）

- 方針: ODE を Volterra 積分方程式 x(t) = x_0 + ∫_0^t [b(s) − H(s)x(s)] ds（(6.181)）の離散化として下三角線形系にし、
  それを §6.3 の QLSP IIR（Thm 6.7）に渡す。MQSP 的な新作業は「Volterra transfer function の選択と条件付け」であり、
  unitary 実現と精度補正は QLSP から継承する（@9030–9036）。
- (a) ネットワーク: `Volterra = SelectFinal(QLSP(A = (B ⊕ I)/4, rhs = |c⟩))`。
  - 正規化サンプル clock |u⟩ = N^{-1/2} Σ_k |k⟩、左求積 J_N = N^{-1} Σ_{0≤l<k<N} |k⟩⟨l|、‖J_N‖ ≤ 1（(6.190)）。
  - 拘束 y^j = |u⟩x^j + hJ_N(b_j − D_jy^j)、x^{j+1} = x^j + h⟨u|(b_j − D_jy^j)、D_j = diag_k H(t_{j,k})、
    b_j = N^{-1/2} Σ_k |k⟩b(t_{j,k})（(6.191)–(6.192)）。E_j = I + hJ_ND_j、‖hJ_ND_j‖ ≤ hα ≤ 1/2、‖E_j^{-1}‖ ≤ 2（(6.182)）。
  - 係数行列 B（(6.194)、初期行に m^{-1/2}I、終状態出力行に τ = r/(4√m W_2)（(6.193)））。
  - ★ oracle adapter: Be[B/4] は「対角減衰（正規化 1）＋端点結合（√2）＋生成子部 h(J_N; ⟨u|)D_j（h α √2）」の 3 項 LCU、
    1 + √2 + hα√2 < 4。J_N は一様補助 index の準備・比較 k ≤ l を失敗 flag・swap・逆準備で実装（(6.196)）。
    1 回の coherent な generator query と O(n + a + log(2mN)) 個の比較・シフト・Hadamard・信号判定 gate。
  - 右辺 |c⟩: 振幅 ‖x_0‖/B の初期 branch と Tβ/B の forcing branch（(6.197)）。A = (B ⊕ I)/4（(6.203)）。
- (c) 解析データ（純粋な有限次元線形代数）:
  - 境界の Schur 補行列: Φ_j = I − h⟨u|D_jE_j^{-1}|u⟩ = (I − δH_{j,N−1})⋯(I − δH_{j,0})（(6.200)）、逆は下三角 (6.201)。
  - ‖X‖ ≤ 4Cm‖e‖、‖Y‖ ≤ 10Cm‖e‖、‖G‖ ≤ 11Cm、‖PG‖ ≤ 4C√m（(6.202)）。
  - ‖B^{-1}‖ ≤ 31CmW_2/r、κ_2(A) ≤ ‖A^{-1}‖ ≤ K := 128CmW_2/r（(6.204)）。
  - 終状態出力の選択確率 > 4/5（(6.205)）、‖A^{-1}|c⟩‖ ≥ R_0 := 4mW_2/B ≥ 4、K/R_0 = 32CB/r（(6.206)）。
  - 離散化: N は (6.189)、細区間の伝播積 ≤ 2C（(6.199)）、格子誤差 ≤ εr/64。
- (d)(e) Thm 6.7 を inverse-state 誤差 min{10^{-3}, ε/256} で適用: Q_H = O(K log(1/ε))、Q_0 + Q_b = O(K/R_0)。
  終出力の条件付けで誤差は高々 8 倍。定数回の試行で成功 ≥ 2/3。gate/qubit は Prop D.7（(6.187)–(6.188)）。
- 多 oracle（§6.4.1, Thm 6.13）: A = A_0 + Σ_ℓ A_ℓ、Be[A_ℓ/λ_ℓ] は H_ℓ を 1 回（(6.213)）、λ_0 = (1+√2)/4、
  λ_ℓ = √2 hα_ℓ/4、ω = (ξ_1/√2, …, ξ_s/√2, Tβ_1, …, Tβ_q)（(6.209)）。率 t_ℓ, u_k は (6.212)、(6.216) で Thm 6.7 の要件を満たす。
- 証明書（§6.4.2–6.4.3）: 平均二乗履歴（Prop D.14、D.15）、尾部（Thm 6.14 = Thm 6.10 の適用）、2 時刻 Green 関数
  （Thm 6.15、Prop D.16）、共通 reducing 部分空間（Thm 6.16、Lemma D.8/D.9）、有限 query 逆近似（Prop 6.17、Lemma D.18）、
  時間変換 y(u) = x(t(u))（(6.239)、Thm 6.18、Cor 6.19）。
- (f) 注意: §6.4 に MQSP の新 module はない。必要なのは「既知の係数演算子 ⊗ oracle の和」で線形系を書く IR と、
  右辺を準備 oracle の重み付き和として書く IR（§6 の F8）。

### 2.11 §6.5 一般化固有値推定（Thm 6.20, 6.21, Prop D.19）

- スカラー設計: q(a,b) = (b + ia/R)/(b − ia/R)、H(z; a,b) = 1/(1 − zq(a,b)) = Σ_k z^k q^k（(6.245)）。
  係数 e^{ikθ}、θ = 2 arctan(a/(Rb))。Kaiser 振幅で重み付けすると位相推定の応答になる。
- 行列版: V = (I − iℋ/R)^{-1}(I + iℋ/R)、W = (B − iA/R)^{-1}(B + iA/R) = B^{-1/2}VB^{1/2}、ℋ = B^{-1/2}AB^{-1/2}（(6.246)）。
  目標 Σ_k c_k|k⟩W^k|ψ⟩ = Σ_k c_k e^{ikθ}|k⟩⊗|ψ⟩（(6.247)）。
- (a) ネットワーク: `GEVP = Median_{⌈50 log(1/δ)⌉}(Readout(FirstSuccess_{≤8}(QLSP(M_N, |0,c,ψ⟩))))`。
  - ★ Cayley 履歴線形系: sz^0 = |c,ψ⟩、(I⊗B − iE_t⊗A/R)z^t = (I⊗B + iE_t⊗A/R)z^{t−1}（(6.250)）、
    M_N = sP_0⊗I⊗I + (I − P_0 − S_N)⊗I⊗B − (i/R)(D_E + T_E)⊗A（(6.254)）、E_t は (6.249)、N = 2n、
    s = β√(κ_B/N)（(6.251)）。Kaiser 状態は右辺の一部。
- (c) 解析データ: 固有状態に対し M_N^{-1}|0,c,ψ⟩ = s^{-1} Σ_t Σ_k c_k e^{i min{k,t}θ}|t,k,ψ⟩、ノルム N/(β√κ_B)（(6.256)）。
  逆の各ブロックは (I⊗B^{-1/2})U_{t,u}(I − iE_u⊗ℋ/R)^{-1}(I⊗B^{-1/2})（ノルム ≤ β^{-1}、(6.257)）、‖M_N^{-1}‖ ≤ K := 2N/β（(6.258)）。
- (d)(e) Thm 6.7 を強度 µ_0 = s、µ_A = 2α_A/R、µ_B = 2α_B（(6.259)）、K = 2N/β、ρ_0 = N/(2β√κ_B)、τ = 1/100（(6.255)）で適用。
  率 t_j = 1 + 3Kµ_j、u = 1 + K/ρ_0、Q_A = O(Kµ_A log(1/τ))、Q_B = O(Kµ_B log(1/τ))、Q_ψ = O(K/ρ_0) = O(√κ_B)（(6.260)）。
  N = O(R/ε) で per-attempt の主張になる。
- readout: 時刻 t ≥ n − 1 を受理、位相 register に shifted inverse Fourier、位相を [−π/2, π/2] に clip、λ̂ = R tan(θ̂/2)。
  Kaiser 窓 (6.248): n = O((R/ε) log(1/η)) で Pr(循環位相誤差 > ε/R) ≤ η（[BTK+25]）。1 回の推定は ≤ 8 回の新しい QLSP、
  ⌈50 log(1/δ)⌉ 回の中央値、得点 X（(6.261)）で E X > 1/5、Hoeffding。
- 増幅版（付録 D.8、Thm 6.21）: padded 履歴 N = 3n（(D.129)–(D.133)）、★ rational metric reweighting
  f_ℓ(b) = √(t_ℓ/β) b/(b + t_ℓ)、t_ℓ = β2^ℓ、L = ⌈log2 κ_B⌉、b/(4β) ≤ Σ_ℓ f_ℓ(b)^2 ≤ 2b/β（(D.134)–(D.135)）、
  補助行 (βI + 2^{-ℓ}B)y^ℓ = 2^{-ℓ/2}BΠ_cz（(D.137)）、L_N（(D.138)）、‖L_N^{-1}‖ ≤ 5N/β（(D.139)）、
  事象確率 q/20 ≤ Pr ≤ 8q（(D.141)）。成功確率の下界 a_0 を使う randomized Grover（(D.144)–(D.145)）。
- (f) 注意: B^{-1/2} を合成せずに元の A, B port のまま履歴を作るのが要点。GEVP 自体も「線形系 IR → QLSP」の再利用例。

### 2.12 §6.6 基底状態準備とエネルギー推定（Thm 6.22, Prop 6.23, 6.24）

- 前提: Be[H/λ] は self-inverse で signal 状態 |0⟩_H、B, B† は制御付き。閾値 −1 ≤ u < v ≤ 1、E_0/λ ≤ u < v ≤ E_1/λ、
  d = arccos u − arccos v。または gap E_1 − E_0 ≥ γ_0、端点 E_0/λ ≥ −1 + β、d_* は (6.267)（β = 0 なら d_* = 2 arcsin(γ_0/(2λ))）。
- 共通 module:
  - Sign の重み評価: L_{Be[A]}(v) ≤ ⟨v, (I + |A|^{-1})v⟩（(6.269)、2 matching layer、(5.32) と Thm 2.1 から）。
  - ★ Normalize: |ω⟩ = V|0⟩、a = ⟨ω|Π|ω⟩。A = (R_ω + R_Π)/2 は span 上で A^2 = aI、A|ω⟩ = Π|ω⟩（(6.270)–(6.271)）。
    F_Normalize(z) = F_s(z; A)、F_Normalize(1)|ω⟩ = Π|ω⟩/√a（(6.272)）。Be[A] は ★ Choice:
    S_choice = [[0, H_c], [H_c, 0]]、Z = R_ω ⊕ R_Π、F_choice = H_cZH_c = Be[A]（(6.273)）、R_ω = V(2|0⟩⟨0| − I)V†。
    状態準備・射影反射・その他の私的接続の catalyst 重みはすべて O(a^{-1/2})。
  - qubitized walk W = R_H Be[H/λ]、R_H = 2|0⟩⟨0|_H − I（(6.275)）。★ half-angle walk U_{1/2} = [[0, W], [I, 0]]_t、
    V_± = −ie^{±iθ_c/2}U_{1/2}（(6.276)）、U_{1/2}^2 = I_t ⊗ W。
  - ★ RealPart: S_real = [[0, Z_bH_b], [H_b, 0]]、Z = V ⊕ V†、F_real = Z_bH_b diag(V, V†)H_b = Be[Re V]（(6.277)）。
    F_real = (1/2)[[V + V†, V − V†], [V† − V, −V − V†]] は Hermitian involution（(6.278)）。
  - ★ Ground = `Series(Sign(RealPart(V_−)), Sign(RealPart(V_+)))`、F_Ground(z_−, z_+) = F_s(z_+; Re V_+) F_s(z_−; Re V_−)（(6.279)）。
    恒等式 sgn sin(ϕ + θ_c/2) · sgn sin(ϕ − θ_c/2) = sgn(cos θ_c − cos 2ϕ)（(6.274)）で F_Ground(1,1) = 2Π_g − I（符号化 signal 部分空間上）。
    sign gap ≥ sin(d/4) は全レジスタ空間で成立、catalyst 重み O(d^{-1})。
  - ★ Filter: S_filter = [[0, H_f], [H_f, 0]]、Ô(z) = I ⊕ F_s(z; A_+)F_s(z; A_−)、F_filter = H_fÔH_f（(6.283)）。
    z=1 で zero-flag block は Π_g。
- 閾値版のレシピ:
  - 候補: `Cand = Substitute(Normalize(V = B); R_Π := Ground)`。z=1 で A_g = |ψ⟩⟨ψ| + Π_g − I（(6.280)）、
    A_g^2 = pI（span 上）、F(1)|ψ⟩ = Π_g|ψ⟩/√p（(6.281)）。重み: 準備 O(p_0^{-1/2})、Hamiltonian O(d^{-1}p_0^{-1/2})。
  - compile: 遅延 r_B = r_B̄ = Θ(d^{-1})、r_H = 1、Σ_j r_jL_j = O(d^{-1}p_0^{-1/2})、一様 clock（Thm 3.2、(3.20)–(3.21)）で定数誤差。
    q_B(C_0) = O(p_0^{-1/2})、q_H(C_0) = O(d^{-1}p_0^{-1/2})（(6.282)）。
  - filter: (6.284) 0 ⪯ F†F'(1) ⪯ O(h^{-1})I、|z| ≥ 1 で ‖F(z)‖ ≤ |z|^{O(h^{-1})}、ζ = Θ(h)。Thm 3.9 で a = h_− = 0、
    w, h_+ = O(h^{-1})、M_loc = 1、horizon O(h^{-1} log(1/η))。‖K̃_η − cΠ_g‖ ≤ η、q_B = 0（(6.285)）。h = sin(d/4)。
  - 合成: √s ≥ c‖Π_gv‖ − η = Ω(1)、(1/2)‖ρ − |g⟩⟨g|‖_1 ≤ η/√s（(6.286)）→ (6.287)。
- gap 版のレシピ:
  - ★ Round: M = Θ(d_*^{-1})（2^k、2π/M ≤ d_*/8）、Mϑ/(2π) = k + t、R(ϑ) = T^k[cos^2(πt/2)I + sin^2(πt/2)T]（(6.289)）。
    Fourier 係数 b_{φ,ℓ} = −π^2 sin φ / ((φ + 2πℓ)[(φ + 2πℓ)^2 − π^2])、|b| ≤ 1、|ℓ| ≥ 2 で |b| ≤ |ℓ|^{-3}（(6.291)）。
    branch 状態 |χ_φ⟩（(6.292)）、S_branch = [[0, U_χ†], [U_χ, 0]]、Ô_branch = [⊕_ℓ sgn(b_{φ,ℓ}) W^{Mℓ+r}] ⊕ I ⊕ (−I)、
    F_branch = U_χ†Ô_branchU_χ（(6.293)）。catalyst 重み O(M)。有限化は |ℓ| ≤ J で打ち切り（誤差 O(J^{-1})）、
    U_χ を反射 I − 2|d_φ⟩⟨d_φ| で実装（(6.306)）。
  - ★ Select: V = B → Round → key 計算（失敗 key を最大に）、V|0⟩ = Σ_x √π_x|x⟩|φ_x⟩（(6.295)）。stop 重み η_0 = Θ(p_0)、
    U_Ω（(6.296)）、現在 key x で Normalize N_x（Π_x は stop または y < x を受理）、経路置換 R_route、
    S_step = [[0, 0, R_route], [I, 0, 0], [0, I, 0]]、Z = U_Ω ⊕ N_x、F_step = R_routeN_xU_Ω（(6.297)）、
    F_Select(z) = D_out(I − zK_next)^{-1}(|∅⟩⊗V)（(6.298)、到達可能部分空間では高々 m 項）。
    出力則 Pr(stop | x) = η_0/(η_0 + P_{x−1})、Σ_{y≤x} w_y = (1 + η_0)P_x/(η_0 + P_x)（(6.299)–(6.302)）、
    重み Σ_x r_x/√a_x = O(η_0^{-1/2})（(6.303)）、proposal span 上の rounder 重み O(M)（(6.304)）。
  - compile: r_B = r_B̄ = M、r_H = 1、一様 clock、N = O(Mp_0^{-1/2})、q_B = O(p_0^{-1/2})、q_H = O(d_*^{-1}p_0^{-1/2})（(6.305)）。
  - ★ Median: U_med|y_1..y_n⟩|0⟩ = |y_1..y_n⟩|median⟩（(6.307)、公開 module、S = F = U_med、oracle コスト 0）。
    n = Θ(log(1/ε)) 個の独立標本で τ = Pr(|θ̂ − θ_0| > d_*/8) ≤ e^{−Ω(n)}（(6.308)、Hoeffding）、cut は (6.309)、
    filter（h = sin(d_*/8)）、誤差 (1/2)‖ρ − |g⟩⟨g|‖_1 ≤ η/√s + τ/s（(6.312)）→ (6.313)。
- エネルギー推定: Prop 6.23 は準備成功後に W へ Kaiser QPE、q_H^{phase} = O((λ/ε_E) log(1/q))、q_B^{phase} = 0（(6.316)）。
  Prop 6.24 は M = Θ(λ/ε_E) の Round + Select 標本器の label を測って中央値を取る（filter 不要）。
- gate/space: (6.288)、(6.314)。

