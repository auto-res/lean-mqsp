# mQSP 応用編 (§7, §8, App. E) 定理インベントリ

対象: Low, "Multivariate Quantum Signal Processing" (arXiv:2610.01125, Draft v8.5)。§7 Quantum simulation of
downfolded Hamiltonians (paper.txt 11311–13562), §8 Online MQSP (13562–14590), App. E Downfolding and online
extensions (19244–19470)。参照した設計: `design-sketch.md` (v0)。式番号は論文のもの。行番号は pdftotext の行番号。

表記: Be[A/λ] は block encoding。`H = [[A,B],[B†,K]]`, `H_eff = A − B K⁻¹ B†`, `X = −K⁻¹B†` (内部応答),
`V = (I, X)ᵀ` (消去写像)。`Q_i` は内部セクタ射影, `Q_0 = P` (active)。`ϱ_i ≥ ‖Q_i X‖`, `ϱ_0 = 1`。
`χ_j = ϱ_i²` (対角成分) / `2 ϱ_i ϱ_k` (結合対) は感度重み, `κ_j ≥ 1` は条件付け因子 (式 7.4 または 7.32 を満たす)。
`L_X(E) = Σ_{o,i} X_{oi} E_{oi}` はクロック抽出, `‖X‖_*` は核ノルム。

---

## 1. 概要

### 1.1 §7 ダウンフォールディングされたハミルトニアンのシミュレーション

- **問題**: Hermitian 模型 `H = Σ_j H_j` を active 空間 P と内部空間 Q に分割し, Schur 補元 (Feshbach–Schur map,
  Kron reduction) `H_eff = A − B K⁻¹ B†` による時間発展 `e^{i t H_eff}` を, 仮想波動関数の準備も別個の線形方程式
  ソルバも使わずに実装する。内部セクタは MQSP ネットワークの **内部フィードバック (Close)** として閉じ,
  その結合方程式の解 (catalyst) が自動的に `K⁻¹B†` 応答を担う。K は不定値でもよい。
- **アクセスモデル**: 各成分 H_j は台 Π_j (単一セクタ `Q_i` か対 `Q_i+Q_k`) を持ち, 制御付き **involution**
  block encoding `Be[H_j/λ_j]` (自己逆, `λ_j ≥ ‖H_j‖`, コスト C_j) で与えられる (7.2)。古典的に与えられる界:
  ギャップ `‖K⁻¹‖ ≤ 1/Δ`, セクタ応答 `ϱ_i`, 条件付け `κ_j` (7.4)。X の成分自体は与えられない。
- **主結果 (Thm 7.1)**: 誤差 ε で `‖U(|0⟩⊗I_P) − |0⟩⊗e^{itH_eff}‖ ≤ ε`, 総重み付きクエリコスト
  `Σ_j C_j q_j = O( |t| (Σ_j sqrt(C_j λ_j χ_j))² + log(1/ε) Σ_j C_j κ_j )`。λ_j が「相関重み付き正規化」
  λ_j χ_j に置き換わるのが要点。データ誤差は `‖Ĥ_eff − H_eff‖ ≤ Σ λ_j χ_j η_j` (Prop 7.10) で配分。
- **派生**: 3成分版 (Cor 7.2), 緩和エネルギー Σ による重み (Cor 7.12), 正定値の場合の逆行列 block encoding
  `Be[(a/4) H_eff⁻¹]` (Cor 7.13; Reciprocal モジュール Lemma 5.7 に閉じたネットワークを Substitute)。
- **§7.2 電子構造**: CAS 周りの励起バンドによる厳密なブロック三重対角形 (7.111), コンパクト粒子–正孔符号化
  (Prop 7.14), スカラー比較行列による応答界 (Prop 7.15), 粗い試行応答からの界 (Prop 7.16), 励起テール除去誤差
  `0 ⪯ H_eff^(k) − H_eff ⪯ ‖R‖²/Δ` (Prop 7.17)。
- **§7.3 Kron reduction**: グラフラプラシアン正則化学習 `M f = b` の Schur 補元 `M_eff` に対し, Cor 7.13 の
  逆 block encoding + 振幅推定で線形スコア `s = (μ/β) Re(z† f)` を推定 (Thm 7.18), コスト
  `C_build + Õ((C_sens + C_fb + C_b + C_z + C_known)/ε · log(2/ϑ))`, `C_sens = (1/a)(Σ_e sqrt(C_e λ_e χ_e))²`,
  `C_fb = Σ_e C_e κ_e`。新しい言語構成は不要 (ダウンフォールディングと同一の feedback-elimination モジュール)。

### 1.2 §8 オンライン MQSP

- **問題**: 既知のシステム行列 S_t と利用可能なオラクル O_{a,t} が物理時刻 (イベント) t ごとに変わる設定。
  古典コントローラは既に得られた記録から S_t を選ぶ。過去のオラクルはイベント後に利用不可, 逆アクセスなし,
  replay なし (外側の振幅増幅も不可)。公開応答は **因果的二時刻カーネル** `H_{t,s}` (一般に Toeplitz でない)。
- **一般論**: 因果リフト `W_N^td = Ŵ_{N−1}⋯Ŵ_0` (Ŵ_j は公開スロット j と共通メモリ M に作用) はユニタリで,
  公開ブロック `K_N = [H_{t,s}]`, `H_{t,t}=A_t`, `H_{t,s}=B_t D_{t−1}⋯D_{s+1} C_s` (t>s), プレフィックス整合
  (Prop 8.1)。二時刻クロック `B_{h,g} = Σ h_t g_s H_{t,s}` は `‖X‖_* ≤ α` で正確に実現でき, 摂動は
  `‖L_X(K) − L_X(K̃)‖ ≤ ‖X‖_* ‖K − K̃‖ ≤ ‖X‖_* min(2, Σ_j ‖W_j − W̃_j‖)` (Thm 8.2)。メモリ減衰は計量 P_j の
  縮小 `D_j† P_{j+1} D_j ⪯ ρ² P_j` から `‖H_{t,s}‖ ≤ C_0 ρ^{t−s−1}` (Prop 8.3)。
- **Kalman (Thm 8.4)**: 構造化異方的モデル `A_t = a_t ⊗ U_t`, `C_t = c_t ⊗ I_N`, `P_t = p_t ⊗ I_N` で共分散・
  ゲインは d×d の古典計算, 高次元輸送 U_t は各イベントで 1 回だけ量子クエリ。重み付き可制御グラミアン
  `g_t = f_t g_{t−1} f_t† + (Y_t²/π_t) k_t k_t†` が各イベントのユニタリ完備と規格化を決め,
  `(⟨0|_ok⊗I) U_alg |0⟩ = μ_T / Z_T`, `Z_T = sqrt(λ_max(g_T))`, `p_succ = ‖μ_T‖²/λ_max(g_T)`。空間
  `w + O(log(d+d_y) + log(T+1))`, 各イベント O(d(d+d_y)) 個の two-level 回転, 中間 postselection なし。
- **付随**: イノベーション条件付け (Lem 8.5), 白色化ユニタリ実現と安定性 (Prop 8.6), 安定性重み付きモデル誤差
  (Thm 8.7, Cor 8.9), 共分散事前分布の感度 (Prop 8.10), 独立オンラインコピーによる成功確率増幅 (Prop 8.8),
  条件付き最終状態保証 (Thm 8.11), 有限メモリ窓 `L = O(log(CM/(εβ_*))/(−log ρ))` (8.60)。

### 1.3 App. E

番号付き命題はない。E.1 は Thm 7.8 (ゲート数) の証明: 内部公開座標を閉じると既知の反射になる (E.3),
閉じたシステム行列 `W_sys = R(I ⊕ P_fb)` (E.4), J 段の同一回転の dyadic 分解 (E.5, [CGJ+26] 引用) によりカスケード長
J が log でしか効かない。E.2 はオンラインカーネルの追加証明書: 凍結更新からの順序積安定性, ランク 2 の
moment-corrected clock (核ノルム (E.8), 誤差 (E.9)), 十分なホライズン (E.10), Bernstein 楕円と時間帯の整合 (E.11)。

### 1.4 §2–5 の一般結果のうち再利用されるもの

| 一般結果 | 応用での使われ方 |
|---|---|
| Thm 2.2 (unitary Toeplitz lift), クエリ数 `⌊(N−1)/r_j⌋` | Thm 7.1 (7.37), Cor 7.13, Thm 7.18; Prop 8.1 は Thm 2.2 の時変一般化 |
| Thm 2.3 / Lemma 2.4 (クロック特性化, 有限カーネル抽出 `‖L_X E‖ ≤ ‖X‖_* ‖E‖`), 式 (2.30)(2.33) 二時刻クロック | Thm 8.2 の本体 (ほぼそのまま) |
| Cor 3.1 (誤差–規格化フロンティア) | (8.10) の SDP 形 |
| Lemma 3.5, 3.6, (3.46)(3.48)(3.72), Thm 3.9 (解析的クロック整形) | Thm 7.1 のホライズン (7.38)(7.39), Cor 7.13 |
| Lemma 3.12 (重み付き遅延配分) | Lemma 7.6 はその「上限付き」版 |
| Thm 3.18 (構成的コンパイル, 有限縮小) | (8.14) オンライン版のコンパイル誤差 |
| (4.98)–(4.101) Schur 補元は accretivity を保つ; Cayley 閉包規則 | Lemma 7.3 の証明の核 |
| Lemma 5.2 (Cayley junction with known load) | Lemma 7.3 の system matrix (7.18) は K_0=0 の特殊形 |
| §5.2 Close (feedback = Schur complement), Substitute, Series, Spectator | Lemma 7.3 (Close), Cor 7.13 (Substitute into Reciprocal), Lemma 7.7 (Series cascade) |
| Lemma 5.7 (Unitary rational reciprocal) | Cor 7.13 |
| Lemma A.2, A.3, A.4 (OAA), Thm A.5, Def A.1, (A.14) | Thm 7.1 (OAA で正規化 2 → ユニタリ), Thm 8.11 (A.3), Thm 7.8/8.4 (資源) |

---

## 2. 定理インベントリ

kind: Thm/Lem/Prop/Cor/Unnum (番号なしだが形式化対象になりうる主張)。difficulty は Mathlib 前提での 1(易)–5(難)。

### 2.1 §7

| ID | kind | short name | category | precise informal statement | one-line proof idea | depends on | used by | proposed Lean home | diff | prio | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 7.1 | Thm | Sensitivity-weighted simulation | application | (7.1)–(7.4) の仮定下, 実 t, 0<ε<1/4 に対し有限ユニタリ回路 U で `‖U(0⊗I_P) − 0⊗e^{itH_eff}‖ ≤ ε`, `Σ C_j q_j = O(abs(t)(Σ_j sqrt(C_j λ_j χ_j))² + log(1/ε) Σ_j C_j κ_j)`; 定数は普遍, 行列オラクルは与えられた Be[H_j/λ_j] のみ | Lemma 7.3 の閉じた Cayley 網 + 指数 IIR; Lemma 7.4 で catalyst 重み, 7.5 で解析半径, Thm 3.9 クロック, 7.6 で遅延配分, 7.7 で有限化, OAA | 7.3–7.7, Thm 2.2, Lem 3.5/3.6, Thm 3.9, Lem A.4, Prop 7.10 (7.5) | 7.2, 7.12, §7.2 (7.113), 7.8 | `MQSP/Apps/Downfolding/Simulation.lean` | 5 | derived | 組み立て定理。核心は 7.3–7.7。O 記法の定数は explicit (7.38)(7.39) で与えられており形式化可能 |
| 7.2 | Cor | Spectral-norm response bound | application | 1 内部セクタ 3 成分 (H_A,H_B,H_K), `‖B‖ ≤ h_B ≤ λ_B`, `‖K⁻¹‖ ≤ 1/Δ`。ϱ=h_B/Δ, χ_A=1, χ_B=2h_B/Δ, χ_K=h_B²/Δ², κ_A=1, κ_B=2λ_B/h_B, κ_K=2λ_K/Δ とすると (7.10)(7.11) のコスト | スケール T_Q=ϱ I_Q で (7.58) を直接計算, (7.59)(7.60) で (7.4) を検証し 7.1 の構成を適用 | 7.1, 7.5, 7.6, 7.7, 7.8 | §7.2 | `MQSP/Apps/Downfolding/ThreeBlock.lean` | 3 | optional | (7.66)–(7.68) の一般スケール s 族も付随 |
| 7.3 | Lem | Schur complement from internal feedback | feedback | 開単位ポリディスク内の z で負荷 `M(z) = Σ_j [ (1−z_j²)/(1+z_j²) Π_j − i 2z_j/(1+z_j²) H̃_j/λ̃_j ]` を定め S(z) をその P 上 Schur 補元とする。各 u>0 に対し既知ユニタリ S_u (7.18) にオラクルを接続し内部セクタ Q_i の公開出力を入力へ戻すと active 応答は `F_u(z) = (I − uS)(I + uS)⁻¹`。S は解析的かつ accretive (Re S ⪰ 0), z=1 へ解析接続され S(1) = −iH_eff; z=1 で `g = T_Q⁻¹ X (x+y)/2`, `y = (I+iuH_eff)(I−iuH_eff)⁻¹ x` | S_u のユニタリ性はブロック乗算; involution で Cayley 変換が (7.20) に; 圧縮和が M; M_QQ 可逆 (Re>0 on supports); 内部入出力を等置し消去; `Re S = V† Re M V ⪰ 0` | Lemma 5.2, (4.98)–(4.101), §5.2 Close | 7.1, 7.4, 7.5, 7.7, 7.13, 7.18, E.1 | `MQSP/Library/SchurFeedback.lean` (代数部は `MQSP/Core/Load.lean`) | 4 | core | **最重要の再利用プリミティブ**。(a) 固定 z の代数的同一性, (b) accretivity, (c) 解析性 に分割可能。K の不定値も可 |
| 7.4 | Lem | Balanced response-weighted normalization | composition | 各 j で `−∂_{z_j} S at z=1 = λ̃_j V† Π_j V ⪰ 0`。s_i = ϱ_i は与えられた ϱ からの上界を全結合同時に最小化。正整数遅延 r で `D_r = Σ r_j λ̃_j Π_j` とすると `0 ⪯ V† D_r V = −(d/dz) S(z^{r_1},…,z^{r_m}) at 1 ⪯ (Σ_j r_j λ_j χ_j) I_P` | 負荷を微分 (恒等係数の微分 −1, 行列係数 0); Schur 補元の微分は V† (·) V; 結合は AM–GM `(s_k/s_i)ϱ_i² + (s_i/s_k)ϱ_k² ≥ 2ϱ_iϱ_k`; 連鎖律 | 7.3 | 7.1, 7.2, 7.5, 7.11 | `MQSP/Library/SchurFeedback.lean` | 3 | core | 閉じた網の group delay (catalyst weight) = V† D V という一般公式。合同変換 T_Q による H_eff 不変性もここで使う |
| 7.5 | Lem | Local analyticity with explicit conditioning | approximation/error | τ̂_r ≥ τ_r = ‖D_{r,Q}^{1/2}(T_Q K T_Q)⁻¹ D_{r,Q}^{1/2}‖ とする。`e^{−tS(z)}` は abs(z)<1 でノルム ≤1, 閉円板 `abs(z−1) ≤ ζ = 1/(64(r_* + τ̂_r))` の近傍で解析的, そこで abs(z)≥1 なら `‖e^{−tS(z)}‖ ≤ abs(z)^{3t Σ r_j λ_j χ_j}`。(7.4) ⇒ τ_r ≤ max κ_j r_j | 対数座標 w で `‖D^{-1/2} M'(w) D^{-1/2}‖ ≤ 2`; 重み付きノルムの Neumann 級数で内部逆の解析性; V(w) の変化評価 (7.29); `‖e^Y‖ ≤ e^{λ_max(Re Y)}` | 7.3, 7.4 | 7.1 (Thm 3.9 の仮定), 7.11, 7.13 | `MQSP/Library/SchurFeedback/Analytic.lean` | 5 | derived | 正定値時は (7.32) も可。演算子値解析関数の Neumann 級数が必要 |
| 7.6 | Lem | Allocation with upper bounds on scaled delays | classical-aux | a_j ≥0, C_j>0, b_0>0, κ_j≥1 に対し `(Σ sqrt(C_j a_j))² + b_0 Σ C_j κ_j ≤ inf_{r∈ℕ_{>0}^m} (Σ C_j/r_j)(Σ a_j r_j + b_0 max κ_j r_j) ≤ 4[同左辺]`; (7.34) が構成的スケジュール | 下界は Cauchy–Schwarz と `max_k κ_k r_k / r_j ≥ κ_j`; 上界は実数解 x_j を最小 1 に正規化し切り上げ (因子 2) | なし (Lemma 3.12 の兄弟) | 7.1, 7.2, 7.13, 7.18 | `MQSP/Aux/Allocation.lean` | 2 | core | 純粋な実数不等式。Lemma 3.12 と同じファイルに。ゲート配分 (7.51)–(7.54) も同型 |
| 7.7 | Lem | Finite realization accurate on the whole clock | approximation/error | J を (7.42) を満たす最小の 2 冪とし u=t/(2J) で Lemma 7.3 の J 段カスケード `F_J(z) = [(I − tS/(2J))(I + tS/(2J))⁻¹]^J` を作ると `‖T_N[F_J] − T_N[e^{−tS}]‖ ≤ ε/4096`, `log J = O(log(1+tΛ_0 N) + log(1/ε))` | 演算子 Schwarz 補題で `‖S(z)‖ ≤ Λ_0 (1+abs(z))/(1−abs(z))`; `‖(I−Z/2)(I+Z/2)⁻¹ − e^{−Z}‖ ≤ ‖Z‖³` (accretive, ‖Z‖≤1) とテレスコープ; `‖T_N[E]‖ ≤ r^{−(N−1)} sup_{abs z=r} ‖E‖` | 7.3, Series | 7.1, 7.8 | `MQSP/Library/CayleyCascade.lean` | 4 | derived | Toeplitz ノルムの円周評価は独立した汎用補題として core に切り出すべき |
| 7.8 | Thm | Gate, oracle, and workspace counts | compilation | アドレス幅 b (7.46) に対し, 増幅回路は (7.40) `q_j = 3⌊(N−1)/r_j⌋` 回の involution 呼び出し, `G_total = O(Σ q_j G_j + N G_align + (m+1) b)`, `n_total = n + O(a_max + s_supplied + log(2+N+J m r_*))` | E.1: 閉じた内部座標は既知反射, 位相を集約, J 個の同一回転を dyadic 分解 (E.5), direct-sum packing (E.6) | 7.1, 7.7, E.1, Thm A.5, Def A.1, [CGJ+26] | 7.2, §7.2 (7.131), 7.13 | `MQSP/Resources/Downfolding.lean` | 5 | optional | ゲート級回路モデルが必要。言語のコスト関数として後回し |
| 7.9 | Prop | Response bounds from a comparison matrix | classical-aux | `‖K_ii⁻¹‖ ≤ 1/Δ_i`, `‖B_i‖ ≤ h_i`, `‖K_ik‖ ≤ h_ik` から比較行列 M (M_ii=Δ_i, M_ik=−h_ik) を作る。M ≻ 0 なら K 可逆, M⁻¹ ≥ 0 成分ごと, `‖K⁻¹‖ ≤ 1/λ_min(M)`, `‖Q_i K⁻¹ Q_k‖ ≤ (M⁻¹)_ik`, `‖Q_i X‖ ≤ Σ_k (M⁻¹)_ik h_k`, `‖BK⁻¹B†‖ ≤ Σ h_i (M⁻¹)_ik h_k` | M = D − H, D^{-1/2}HD^{-1/2} のノルム<1 (非負行列の二次形式) で Neumann 級数; ブロックノルムベクトル u に対し Mu ≤ f_blk | なし | 7.1 の仮定供給, 7.15 | `MQSP/Aux/MatrixAnalysis/Comparison.lean` | 3 | optional | M-行列理論。K の正定値性は不要 |
| 7.10 | Prop | Sensitivity to coarse approximations | approximation/error | 台を保つ摂動 `‖δH_j‖ ≤ λ_j η_j`, 経路 H(s)。(7.4) または (7.32) で `max κ_j η_j < 1 ⇒ ‖K(s)⁻¹‖ ≤ 1/(Δ(1 − s max κ_j η_j))`。経路上で ‖Q_i X(s)‖ ≤ ϱ_i なら `‖H_eff(1) − H_eff(0)‖ ≤ Σ λ_j χ_j η_j`; 両端 ⪰ aI なら逆の差 ≤ (1/a²) Σ λ_j χ_j η_j | Schur 補元の微分 `Ḣ_eff = V† Ḣ V` (7.87) を積分; Neumann 級数; Duhamel で時間発展へ | 7.4 の合同変換 | (7.12), (7.129), 7.18 (7.154) | `MQSP/Aux/MatrixAnalysis/SchurPerturbation.lean` | 3 | derived | 微分を避け有限差の恒等式でも証明可能 |
| 7.11 | Prop | Positive response and inverse bounds | classical-aux | K ≻ 0 なら `Σ = BK⁻¹B† = X†KX`, `ΔI ⪯ K ⪯ dI ⇒ ΔX†X ⪯ Σ ⪯ dX†X`, `‖X‖² ≤ ‖Σ‖/Δ`。H ≻ 0, H_eff ⪰ aI なら `H̃⁻¹ = V H_eff⁻¹ V† + diag(0,(T_Q K T_Q)⁻¹)`, `‖D_r^{1/2} H̃⁻¹ D_r^{1/2}‖ ≤ (1/a)Σ r_j λ_j χ_j + max κ_j r_j` | 二次形式への代入; ブロック逆公式; 7.4 と 7.5 の評価を足す | 7.4, 7.5 | 7.12, 7.13, 7.18 | `MQSP/Aux/MatrixAnalysis/SchurPerturbation.lean` | 2 | derived | ブロック逆の公式は Mathlib の `Matrix.fromBlocks` 系で近いものあり (演算子版が必要) |
| 7.12 | Cor | Relaxation energy with separate spectral bounds | application | 1 内部成分, ΔI ⪯ K ⪯ h_K I, `‖Σ‖ ≤ E`, `‖B‖ ≤ h_B ≤ λ_B`。`ϱ = min(h_B/Δ, sqrt(E/Δ))` が有効で λ_K χ_K ≤ λ_K min(h_B²/Δ², E/Δ), λ_B χ_B ≤ 2λ_B min(·); λ_B ≤ β‖B‖ なら `λ_B χ_B ≤ 2β sqrt(h_K/Δ) E`, `λ_K χ_K ≤ (λ_K/Δ) E`; κ は (7.95) | 7.11 と K² ⪯ h_K K から BB† ⪯ h_K Σ | 7.11, (7.56) | (7.115) | `MQSP/Apps/Downfolding/Relaxation.lean` | 2 | optional | 不定値 K の反例 K=diag(1,−1) が付記 |
| 7.13 | Cor | Positive inverse block encoding with known normalization | application | 7.11 の正定値仮定下, Reciprocal モジュールと共有解析クロック 1 つで `‖B_ε − (a/4) H_eff⁻¹‖ ≤ ε` の Be[B_ε], コスト `O(((1/a)(Σ sqrt(C_j λ_j χ_j))² + Σ C_j κ_j) log(1/ε))`, ホライズン (7.99) | f_d(u)=u^{2d−1}/(1+u^{2d}) を Lemma 5.7 で ≤3d 個のシフト Cayley 因子に; 各因子の負荷に Lemma 7.3 の閉じた網を Substitute; 全因子を同一解析近傍で評価 (7.101); 一つのクロック; 7.6 で配分 | 5.7, 7.3, 7.5, 7.6, 7.11, Thm 3.9, Thm A.5 | 7.18 | `MQSP/Apps/Downfolding/Inverse.lean` | 5 | derived | 「負荷レベルの Substitute」(閉じたネットワークの S(z) を Cayley 因子の信号に代入) が必要 |
| 7.14 | Prop | Compact particle–hole space | classical-aux | core/active/virtual 分割, 置換距離 ≤k の行列式全体 Π_k の次元は (7.109) の三重和, 符号化は `n_act + k⌈log₂(n_core+1)⌉ + k⌈log₂(n_virt+1)⌉ + 2⌈log₂(k+1)⌉ + O(1)` qubit | 距離 = max(h,p); 正孔集合・粒子集合・active 行列式の数え上げ; ソート済みリスト符号化の単射性 | なし | §7.2 資源 (7.131) | `MQSP/Apps/Chemistry/ParticleHole.lean` | 3 | optional | フェルミオン Fock 空間の形式化が前提。組合せ部分のみなら 2 |
| 7.15 | Prop | Scalar bounds for coupled excitation chain | classical-aux | 励起バンド (7.111), `H_i − E ⪰ d_i`, `‖T_i‖ ≤ b_i`。三重対角比較行列 𝒦 ≻ 0 なら `Δ = λ_min(𝒦)`, `‖Q_i X‖ ≤ b_0 (𝒦⁻¹)_{i1}`, `‖Σ‖ ≤ b_0² (𝒦⁻¹)_{11}`; ピボット g_i (7.119) で `‖Q_i X‖ ≤ (b_0/g_1) Π_{k=2}^{i} b_{k−1}/g_k` | ブロック Cauchy–Schwarz `v†Kv ≥ zᵀ𝒦z`; Perron–Frobenius / Neumann 展開のパス比較; 後退代入 | 7.9 と同型 | 7.17 (7.126) | `MQSP/Aux/MatrixAnalysis/Comparison.lean` | 3 | optional | 7.9 の特殊化として統合可 |
| 7.16 | Prop | Response/correlation bounds from coarse approximation | classical-aux | 試行応答 X̂, 残差 R = K X̂ + B†, K ⪰ ΔI_Q なら `‖Q_i X‖ ≤ ‖Q_i X̂‖ + ‖R‖/Δ`; `Σ = Σ̂ + R† K⁻¹ R`, `Σ̂ ⪯ Σ ⪯ Σ̂ + (‖R‖²/Δ) I_P` | X − X̂ = −K⁻¹R; 二次式の展開; 0 ⪯ K⁻¹ ⪯ Δ⁻¹ | なし | 7.17 | `MQSP/Aux/MatrixAnalysis/SchurPerturbation.lean` | 2 | optional | a posteriori 証明書。粗データ版 (7.123) 付随 |
| 7.17 | Prop | Excitation-tail error | approximation/error | K ⪰ ΔI_Q, H_eff^(k) を Π_k H Π_k の厳密ダウンフォールディングとし X̂ を 0 拡張, R = K X̂ + B†。`H_eff^(k) − H_eff = R† K⁻¹ R`, `0 ⪯ · ⪯ (‖R‖²/Δ) I_P`, `‖e^{itH_eff^(k)} − e^{itH_eff}‖ ≤ abs(t) ‖R‖²/Δ` | 7.16 の恒等式で試行自己エネルギーが厳密に A − H_eff^(k); Duhamel | 7.16, 7.15 | (7.130) | `MQSP/Aux/MatrixAnalysis/SchurPerturbation.lean` | 2 | optional | 部分空間削除 (量子レジスタ削減) の唯一の根拠 |
| 7.18 | Thm | Correlation-weighted coarse Kron prediction | application | 粗いグラフ行列 M̄ = Σ_e M̄_e の成分 block encoding, `M̄_eff ⪰ aI` (a ≥ μ), (7.146), バイアス `abs(s − s̄) ≤ ε/2`。逆 block encoding と振幅推定で `abs(ŝ − s) ≤ ε` を失敗確率 ≤ ϑ, コスト (7.148) で返す | 7.11 で (7.150), 7.13 で `Be[(a/4) M̄_eff⁻¹]`, 7.6 で配分, Hadamard test + 振幅推定 [BHMT02], 中央値で信頼度 | 7.11, 7.13, 7.6, Thm A.5 | — | `MQSP/Apps/Kron.lean` | 4 | optional | 振幅推定・確率論層が必要 (core 外)。バイアス (7.149)/(7.154) は 7.10 から |
| U7.a | Unnum | Inverse stability under data error (7.5)/(7.83) | approximation/error | `max_j κ_j η_j < 1 ⇒ ‖K̂⁻¹‖ ≤ 1/(Δ(1 − max κ_j η_j))` | 合同変換後の摂動和 ≤ Δ max κη, Neumann | (7.4) | 7.10 | `.../SchurPerturbation.lean` | 2 | derived | 7.10 の前半として |
| U7.b | Unnum | Internal-only perturbation (7.88) | approximation/error | `H'_eff − H_eff = X† δK X'`, `‖H'_eff − H_eff‖ ≤ ‖X‖² η/(1 − η/Δ)` | resolvent identity | — | §7.2 | `.../SchurPerturbation.lean` | 1 | optional | |
| U7.c | Unnum | Relaxation identity & positive Schur criterion (7.114)(7.124) | classical-aux | `u†(A−E)u − min_{v∈ran Q} (u+v)†(H−E)(u+v) = u†Σu`; `Σ ⪯ E I_P ⇔ [[E I_P, B],[B†, K]] ⪰ 0` | 平方完成; Schur 補元の正値判定 | — | 7.12, 7.16 | `.../SchurPerturbation.lean` | 2 | optional | Mathlib の `Matrix.PosSemidef.fromBlocks` 系に近い |
| U7.d | Unnum | Energy self-consistency (7.132)(7.133) | classical-aux | `d/dE (H_eff(E) − E) = −I − X†X ⪯ −I`; η-近似と残差 ε_solve から `abs(Ê − E_0) ≤ η + ε_solve` | 微分 + Weyl 不等式 + 単調性 | — | — | `MQSP/Apps/Chemistry/Energy.lean` | 3 | optional | |

### 2.2 §8

| ID | kind | short name | category | precise informal statement | one-line proof idea | depends on | used by | proposed Lean home | diff | prio | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 8.1 | Prop | Causal lift and prefix consistency | online | `W_j = S_j (I_P ⊕ Q_j) = [[A_j,B_j],[C_j,D_j]]` を公開スロット j と共通メモリ M に埋め込んだ Ŵ_j の積 `W_N^td = Ŵ_{N−1}⋯Ŵ_0` は `(ℂ^N ⊗ P) ⊕ M` 上ユニタリ。初期メモリ 0 での公開ブロックは `K_N = [H_{t,s}]`, `H_{t,s} = 0 (t<s), A_t (t=s), B_t D_{t−1}⋯D_{s+1} C_s (t>s)`; `K_N†K_N + E_N†E_N = I`, `‖K_N‖ ≤ 1`; `K_N[0:n−1,0:n−1] = K_n` (プレフィックス整合)。連続性・解析性は不要 | 埋め込みのユニタリ性; 右から順に適用し前進代入 `m_t = Σ_{s<t} D_{t−1}⋯D_{s+1} C_s u_s`; 等長性の制限 | なし (Thm 2.2 を一般化) | 8.2, 8.3, 8.4, (8.8), 時不変時に Thm 2.2 | `MQSP/Online/Lift.lean` | 2 | core | **Thm 2.2 をこの系として導く設計を推奨** (§4)。物理順序 (8.3b) も定理の一部 |
| 8.2 | Thm | Input/output-time clock selection and perturbation | online | 正規化クロックは `‖X‖_* ≤ α_clk` の重なり行列をちょうど実現し `L_X[K_N(ω)]/α_clk` を選ぶ; 一様誤差 η の最小規格化は (8.10) の inf; 任意のブロックカーネルで `‖L_X(K) − L_X(K̃)‖ ≤ ‖X‖_* ‖K − K̃‖`; 二つのユニタリ系列で `≤ ‖X‖_* min(2, Σ_{j<N} ‖W_j − W̃_j‖)` | Thm 2.3 と Lemma 2.4 (矩形カーネル可); K − K̃ に Lemma 2.4; 積のテレスコープ (中間ノルム 1) | Thm 2.3, Lem 2.4, Cor 3.1, 8.1 | 8.4, 8.11, (8.14), (8.20), 8.3.7 | `MQSP/Online/Clock.lean` (摂動部は `MQSP/Clock/Kernel.lean`) | 2 | core | 上三角成分 X_{oi} (o<i) も核ノルム完備に必要。因果的クロック準備は別の仮定 |
| 8.3 | Prop | Decay of memory contribution | online | 正定値 P_j が `D_j† P_{j+1} D_j ⪯ ρ² P_j`, `p_− I ⪯ P_j ⪯ p_+ I` (0<ρ<1) を満たせば C_0 = sqrt(p_+/p_−) で `‖D_{t−1}⋯D_s‖ ≤ C_0 ρ^{t−s}`, `‖H_{t,s}‖ ≤ C_0 ρ^{t−s−1}`; メモリ年齢演算子 K_ℓ の生成関数で `sup_{abs z=R} ‖K_N(z)‖ ≤ 1 + C_0 R/(1−ρR)`, `‖Σ_{ℓ≥L} K_ℓ‖ ≤ M_R R^{−L}/(1 − R⁻¹)` (N に一様) | 計量不等式の反復; 同一年齢対角のブロックは入出力スロットが素; 幾何級数; Cauchy 係数評価 | 8.1 | (8.20), (8.60), E.2 | `MQSP/Online/Memory.lean` | 3 | core | 凍結スペクトル半径では不十分 (交互冪零の反例) |
| 8.4 | Thm | Forward-only structured anisotropic Kalman filtering | application | (8.26)(8.27) の下, (8.28) で小行列を更新し g_t を (8.30) とする。g_T ≠ 0 なら `(bra(0)_ok ⊗ I) U_alg ket(0) = μ_T/Z_T`, `Z_T = sqrt(λ_max(g_T))`, μ_T ≠ 0 で `p_succ = ‖μ_T‖²/λ_max(g_T)`。g_T = 0 なら失敗報告。各 U_t を 1 回, 非零重み観測準備を各 1 回, 逆も中間 postselection もなし, 空間 `w + O(log(d+d_y) + log(T+1))`, イベントあたり O(d(d+d_y)) two-level 回転 | テンソル構造で P_t = p_t⊗I_N; 行 `R_t^(g) = [g_t^{-1/2} f_t g_{t−1}^{1/2}, (Y_t/sqrt π_t) g_t^{-1/2} k_t]` が余等長 → 既知ユニタリ S_t に完備 (特異時は台を追加入力で補う); 帰納法でメモリ振幅 `(g_t^{-1/2} ⊗ I) μ_t`; 最後に g_T^{1/2}/Z_T を抽出; (8.35) の凸性 | 8.1, (8.2) の junction, Givens 分解 | 8.8, 8.11, 8.3.7 | `MQSP/Apps/Kalman/Filter.lean` | 4 | derived | (8.33)–(8.36) の Gramian 展開・凸最適化・包絡線選択 `Z_T ≤ Σ β_s` を含む。等方特殊化 (8.37) |
| 8.5 | Lem | Innovation conditioning | classical-aux | 予測共分散 ≤ p, 観測行列 ≤ c, イノベーション ⪰ λI のとき `δK ≤ (c δP⁻ + p δC)/λ + (pc/λ²)(c² δP⁻ + 2pc δC + δR)` | `V⁻¹ − Ṽ⁻¹ = V⁻¹(Ṽ − V)Ṽ⁻¹` と三角不等式 | — | 8.7 の入力 | `MQSP/Apps/Kalman/Sensitivity.lean` | 2 | optional | 純粋な行列摂動 |
| 8.6 | Prop | Covariance storage and unitary realization | classical-aux | P_t ≻ 0, R_t ≻ 0 で N_t (8.43), `D_t = P_t^{-1/2} F_t P_{t−1}^{1/2}`, `B_t = P_t^{-1/2} K_t R_t^{1/2}`。`P_t = F_t P_{t−1} F_t† + N_t`, 行 `[D_t B_t]` は縮小, Julia 型完備 J_t (8.44) はユニタリで白色化平均を写す (8.45)。(8.46) の下 `‖U(t,s)‖ ≤ C ρ^{t−s}`, `ρ = sqrt(1−η)` | Joseph 形式の展開と白色化; 行縮小の Halmos/Julia ダイレーション (SVD); 平方根のテレスコープ | 8.3 型の議論 | 8.7, (8.60) | `MQSP/Apps/Kalman/Whitening.lean` (完備は `MQSP/Core/Dilation.lean`) | 3 | derived | 行縮小のユニタリダイレーション自体は core 級プリミティブ |
| 8.7 | Thm | Stability-weighted model error | approximation/error | 実装プロパゲータが `‖Ũ(t,s)‖ ≤ C ρ^{t−s}` なら `‖μ̃_T − μ_T‖ ≤ Cρ^T e_0 + C Σ_t ρ^{T−t}(δF_t ‖μ_{t−1}‖ + δK_t ‖y_t‖ + ‖K̃_t‖ δy_t)` | 差の漸化式を F̃_t で伝播 (離散 Duhamel) | 8.6 | 8.9, 8.11 | `MQSP/Online/Stability.lean` | 2 | derived | 一般の時変 IIR に対する汎用評価として書ける |
| 8.8 | Prop | Success from independent online copies | online | 記録を固定し各コピーの成功確率 ≥ p_*, 条件付き出力が目標から trace distance ≤ ε, 実装がコピー間で分解するなら m コピーで最初の成功を選ぶと `Pr[all fail] ≤ (1−p_*)^m ≤ e^{−m p_*}`, `D(ρ_sel, τ_T) ≤ ε`; `m = ⌈p_*⁻¹ log(1/ϑ)⌉` | 条件付き独立性; 1−p ≤ e^{−p}; trace distance の凸性 | Lemma A.3 型 | 8.11 後, (8.63)–(8.65) | `MQSP/Online/Copies.lean` | 3 | optional | 測定・確率の意味論層が要る。replay 不可モデルでの唯一の増幅手段 |
| 8.9 | Cor | Explicit drift bound (scalar filter) | approximation/error | ゲイン ∈ [γ, k_+] ⊂ (0,1], ρ = 1−γ, M = max(M_0, Y) で `E_T^model ≤ ρ^T e_0 + Σ_t ρ^{T−t}[ρ M d_t + (M+Y) h_t + k_+ o_t]`, 一様なら ≤ [ρMd + (M+Y)h + k_+ o]/γ | 凸結合更新で ‖μ_t‖ ≤ M; 8.7 に代入 | 8.7, (8.52) | — | `MQSP/Apps/Kalman/Sensitivity.lean` | 2 | optional | 凍結比較 `M ν_U ρ²/γ²` も付随 |
| 8.10 | Prop | Sensitivity of scalar covariance prior | classical-aux | (8.37) の二つの再帰, ゲイン ∈ [γ,k_+], イノベーション ≥ σ で `δp_t ≤ ρ² δp_{t−1} + ρ² δq_t + k_+² δv_t`, `h_t ≤ (δp_{t−1} + δq_t + δv_t)/σ`, 一様誤差なら (8.56) | f(s,v) = sv/(s+v) の偏微分 `∂_s f = (1−k)² ≤ ρ²`, `∂_v f = k² ≤ k_+²` を線分上で積分 | — | 8.9 | `MQSP/Apps/Kalman/Sensitivity.lean` | 2 | optional | |
| 8.11 | Thm | Conditional final-state guarantee | approximation/error | β = ‖μ_T‖ > 0, 規格化 Z, 回路誤差 η_circ, 切断誤差 E_trunc, `E = E^model + E_trunc + Z η_circ < β` なら選択出力 ρ̂_T は `D(ρ̂_T, μ_Tμ_T†) ≤ 2E/β`, `p_succ ≥ (β−E)²/Z²`; E ≤ εβ/2 なら誤差 ≤ ε, 成功 ≥ 1/(4χ²) | ユニタリ誤差 → 選択ベクトル誤差; Z 倍; Lemma A.3 | Lem A.3, 8.7, (8.60) | 8.8 と組合せ | `MQSP/Online/Guarantee.lean` | 2 | derived | 非干渉ノイズの拡張 (2ν/p_*) も付記 |
| U8.a | Unnum | Online compile error (8.13)(8.14) | compilation | `sup_ω ‖L_X(K_N) − T(ω)‖ ≤ ε_des`, `sup ‖K̂_N − K_N‖ ≤ η_N`, `‖X‖_* ≤ α` ⇒ `Be[T̃/α]`, `‖T̃ − T‖ ≤ ε_des + ‖X‖_* η_N + α η_syn` | Thm 3.18 の有限縮小証明 | Thm 3.18, 8.2 | 8.11 | `MQSP/Online/Clock.lean` | 2 | core | 補正項はオンラインのクエリ順序を守る場合のみ |
| U8.b | Unnum | System-matrix drift (8.15) and Duhamel (8.51)(8.52) | approximation/error | `‖W_j − W̃_j‖ ≤ ‖S_j − S̃_j‖ + Σ_a ‖O_{a,j} − Õ_{a,j}‖`; `‖e^{−iτH} − e^{−iτH̃}‖ ≤ min(2, abs(τ) ‖H − H̃‖)` | 積の三角不等式; Duhamel | — | 8.2 (8.12), 8.9 | `MQSP/Online/Stability.lean` | 1 | derived | |
| U8.c | Unnum | Memory-age & Chebyshev truncation (8.20) | approximation/error | Bernstein 楕円 E_χ 上 `sup ‖B_ℓ‖ ≤ M R^{−ℓ}` なら年齢 L−1, 次数 p 切断で `‖K_N − K̃_N‖ ≤ M R^{−L}/(1−R⁻¹) + 2Mχ^{−p}/((χ−1)(1−R⁻¹))` | Chebyshev 係数評価を年齢と次数で二重和 | 8.3 | E.2 | `MQSP/Online/Memory.lean` | 4 | optional | Chebyshev 近似論が必要 (Mathlib 薄い) |
| U8.d | Unnum | Finite memory window (8.60)(8.61) | approximation/error | (8.46)(8.47), ‖μ_t‖ ≤ M で T−L から開始すれば `E_trunc ≤ C M ρ^L`, `L = min(T, ⌈log(4CM/(εβ_*))/(−log ρ)⌉)`; 生成関数 `sup_T sup_{abs z=R} ‖G_T(z)‖ ≤ C k_+/(1−ρR)` | 幾何的減衰 | 8.6 | 8.11, (8.63)–(8.65) | `MQSP/Apps/Kalman/Window.lean` | 2 | optional | 古典共分散再帰は全期間継続する点に注意 |

### 2.3 App. E (番号なし)

| ID | kind | short name | category | precise informal statement | one-line proof idea | depends on | used by | proposed Lean home | diff | prio | notes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| E.1a | Unnum | Closed internal coordinate is a known reflection (E.2)(E.3) | feedback | u=t/(2J) の junction はセクタ Q_i と結合範囲上で 2×2 ユニタリ `[[c_i, −i sqrt(1−c_i²)],[sqrt(1−c_i²), i c_i]] ⊗ I_{Q_i}`, `c_i = (1−uΛ_i)/(1+uΛ_i)` として作用; 公開入出力を等置すると private 出力は `−i v` (既知反射) | 2×2 の消去計算 (K⁻¹ 演算不要) | 7.3, 等長 V_i (E.1) | E.1b, 7.8 | `MQSP/Library/SchurFeedback/Circuit.lean` | 2 | core | **「identity Close の閉システム行列は既知ユニタリ」**の具体例。一般補題化を推奨 (§3) |
| E.1b | Unnum | Closed system matrix factorization (E.4)(E.5) | compilation | `W_sys = R (I_public ⊕ P_fb)`, `P_fb = i(I − 2 Σ_i V_i V_i†)`; J 段の位相を集約し, 同一回転 J 個の積を dyadic 分解 (段アドレス 1 bit ごとに制御 1-qubit ゲート) | 位相の可換性; [CGJ+26, Lemma 10, Prop 11] | E.1a | 7.8 | 同上 | 4 | optional | 外部文献の結果を仮定として取り込む候補 |
| E.1c | Unnum | Direct-sum packing & counts (E.6) | compilation | リフトは `(ℂ^N⊗P) ⊕ ⊕_j (ℂ^{r_j} ⊗ ℂ^J ⊗ L_j)` 上; 成分 j の 1 回の呼び出しが全段に作用 (段は spectator); 既知操作 O(N[G_align + (m+1)b]) | パディングと二進ラベル付け替え | E.1b, Thm A.5 | 7.8 | `MQSP/Resources/Downfolding.lean` | 4 | optional | ポート多重度 (stage⊗delay) を言語が表現できる必要 (§4) |
| E.2a | Unnum | Memory stability from frozen updates | online | `‖D(t)^r‖ ≤ C_f ρ_f^r`, 隣接差 ≤ ν, `q_b = C_f ρ_f^b + ν b(b−1)/2 < 1` ⇒ `‖D_k⋯D_{k−r+1}‖ ≤ q_b^{⌊r/b⌋}`; 解析接続下で Cauchy 評価により τ_L = M R^{−L}/(1−R⁻¹) | b 個ずつのテレスコープ | 8.3 | — | `MQSP/Online/Memory.lean` | 2 | optional | |
| E.2b | Unnum | Moment-corrected rank-two clock (E.7)–(E.9) | online | Legendre 基底で補正重み c^(c) を作り, `X_{k,s} = c_k^(0) 1_{I_0}(s) + c_k^(c) 1_I(s)` はランク ≤2, `‖X‖_* ≤ α_0 + α_c`; 次数 p 多項式近似誤差 E_p なら `‖L_X[K] − F(t_*,1)‖ ≤ (1+β)τ_L + (2+β)E_p` | 次数 p までのモーメント再現; 各矩形がすべての年齢 <L を含む | 8.2, E.2a | — | `MQSP/Online/MomentClock.lean` | 4 | optional | |
| E.2c | Unnum | Normalization 1+δ and horizons (E.10)(E.11) | online | m_0, m の選択で規格化 ≤ 1+δ, `N_centered = O(L + p + L(p+1)^{5/2}/δ^{3/2})`, `N_trailing = O(L + p + L(p+1)³/δ²)`; 楕円が時間帯に入る条件 `a(χ − χ⁻¹)/2 < σ` | Legendre 微分評価, 離散 Gram 行列 1/2 I ⪯ H_p ⪯ 3/2 I | E.2b | — | 同上 | 5 | optional | 定数追跡が重い。形式化優先度は最低 |

**統計**: 番号付き命題は §7 で 18 (Thm 3, Lem 5, Prop 7, Cor 3), §8 で 11 (Thm 4, Lem 1, Prop 5, Cor 1), App. E で 0。
表には番号なし主張を §7 で 4, §8 で 4, App. E で 6 追加 (計 43 行)。

---

## 3. 再利用可能なプリミティブ (core ライブラリ候補)

化学・グラフ・Kalman に依存しない汎用命題で, core に置く価値があるもの。

1. **Prop 8.1 (因果リフト)** — `Fin N →` ユニタリ系列 W_j の積がユニタリで, 公開ブロックが下三角カーネル
   `H_{t,s} = B_t D_{t−1}⋯D_{s+1} C_s` を持ちプレフィックス整合。理由: Thm 2.2 (unitary Toeplitz lift) は定数系列の
   特殊化であり, 一つの証明で時不変・時変の両方を得られる。証明は帰納法と前進代入のみ (難易度 2)。
2. **Thm 8.2 / Lemma 2.4 のカーネル版 (クロック抽出と摂動)** — `‖L_X(K) − L_X(K̃)‖ ≤ ‖X‖_* ‖K − K̃‖` と
   ユニタリ系列のテレスコープ `≤ ‖X‖_* min(2, Σ ‖W_j − W̃_j‖)`。理由: すべてのコンパイル誤差予算
   (ゲート合成誤差, ドリフト, 切断) がこの二式に帰着する。U8.a (8.14) も同所に。
3. **Lemma 7.3 (内部フィードバックによる Schur 補元)** — 正確には次の 3 つに分解して core 化する:
   (a) 負荷の代数: accretive 負荷 M に対し Schur 補元 `M/M_QQ` も accretive (`Re S = V† Re M V`), Cayley
   `(I − uS)(I + uS)⁻¹` は縮小 ((4.98)–(4.101) と共通);
   (b) Close の同一視: Cayley junction の公開セクタ Q を恒等フィードバックで閉じた応答 = 閉じた負荷の Cayley;
   (c) 正則な恒等 Close の閉システム行列は既知ユニタリ (E.1a の一般化。Redheffer star product の
   ユニタリ性)。理由: Kron reduction, Reciprocal 内の Substitute (Cor 7.13), D 章の constraint system も同じ構造。
4. **Lemma 7.4 (閉じた網の catalyst 重み公式)** — `−(d/dz) S(z^r) at 1 = V† D_r V` と合同変換
   `B T (T K T)⁻¹ T B† = B K⁻¹ B†` による規格化の再配分。理由: 任意の Cayley/Schur ネットワークの group delay
   を消去写像で表す一般則で, Thm 3.9 への入力 (W の上界) を与える標準手段。
5. **Lemma 7.6 (上限付き平方根配分)** — Lemma 3.12 と並ぶ純粋な実数最適化。理由: precision 項
   `b_0 max κ_j r_j` を持つ全ての重み付きコスト定理 (7.1, 7.13, 7.18, おそらく §6 の多数) で使える。易しい。
6. **Toeplitz ノルムの円周評価 (Lemma 7.7 内)** — `‖T_N[E]‖ ≤ r^{−(N−1)} sup_{abs z=r} ‖E(z)‖` と
   Cayley 対 exp の 3 次評価 `‖(I − Z/2)(I + Z/2)⁻¹ − e^{−Z}‖ ≤ ‖Z‖³` (accretive, ‖Z‖≤1)。理由: 「伝達関数の
   近似を Toeplitz ブロック全体の近似に変換する」汎用道具で, 有限実現 (Exp, HamSim の有限化) に再利用される。
7. **Schur 補元の摂動・逆公式 (Prop 7.10 の (7.87), Prop 7.11 の (7.90), Prop 7.16 の残差恒等式)** —
   `dH_eff = V† dH V`, `H⁻¹` のブロック表示, `Σ = Σ̂ + R†K⁻¹R`。理由: 古典補助だが §7 全体と Kron で共有される
   行列解析の基盤。`MQSP/Aux/MatrixAnalysis` に置く。
8. **Prop 8.3 (計量縮小によるメモリ減衰)** — 時変 IIR の順序積評価。理由: オンライン切断誤差の標準形で,
   Kalman (8.47) と E.2 が同型。凍結スペクトル半径との区別を定理として持つ価値がある。
9. **行縮小のユニタリ完備 (Prop 8.6 の (8.44), Thm 8.4 の行完備)** — `[R ; (I−R†R)^{1/2}]` 型の Julia
   ダイレーション。理由: 既知 junction を「縮小行から作る」汎用構成で, QSP 完備や Lemma 5.7 とも関連。
10. **Prop 8.8 (独立コピー)** — replay 不可モデルでの成功確率増幅。測定意味論層が入るなら core の
    `Online` に置く (optional)。

非プリミティブ (アプリ層に留める): 7.1, 7.2, 7.8, 7.12–7.18, 8.4, 8.5, 8.7, 8.9–8.11, E.1b/c, E.2b/c。

---

## 4. 設計へのフィードバック

### 4.1 §7 が言語に要求するもの

- **負荷 (Load) 層**: Lemma 7.3 と Cor 7.13 は「伝達関数」ではなく **accretive な解析的負荷 M(z)** の代数
  (正和, 既知合同変換, Schur 補元) と, それを Cayley 変換で module 化する操作で書くのが自然。提案:
  `structure Load` (公開空間, ポート, 解析的 accretive 関数 + Cayley junction 実現) と
  `Load.add / Load.congr (T) / Load.schur (Q) / Load.cayley (u) : Module`。Lemma 7.3 は
  `cayley u (schur Q (Σ_j weightedLoad_j))` の意味論定理になる。Thm 4.9 直後の閉包規則 ((4.98)–(4.101), paper.txt 5292 行) と共通。
- **恒等 Close (遅延・marker なしの内部フィードバック消去)**: sketch の Close は `wV` 付きの feedback だが,
  §7 では marker なし (w=1) で公開セクタを閉じる。正則性仮定 (`I − F_ee` が解析領域で可逆) と,
  閉システム行列が既知ユニタリになること (E.1a) の二つを Close の定理として持つ必要がある。
- **ポート共有カスケード**: Lemma 7.7 の J 段カスケードは同じ成分オラクルを各段で使うが, E.1c では 1 回の
  呼び出しが `ℂ^J ⊗ L_j` 上で全段に作用する (段レジスタは spectator)。sketch の `Fin r_j ⊗ K j` (遅延) を
  一般化した **ポート多重度** (private 空間 `Fin c_j ⊗ K j`, クエリは `I ⊗ O_j`) と, 同一変数を共有する
  Series (変数同一視) が必要。クエリ数は `q_j` のままで多重度は回数に入らない点を cost 関数に反映すること。
- **負荷レベルの Substitute**: Cor 7.13 は Reciprocal (Lemma 5.7 のシフト Cayley 因子列) の各因子の信号に
  閉じたネットワーク S(z) を代入する。Substitute の対象を「Hermitian 信号を持つ module」に拡げるか, Reciprocal を
  Load を引数に取る形で定義する。
- **involution オラクル**: (7.2b) `Be† = Be, Be² = I` を OracleSig の Promise として表現 (sketch の Promise で可)。
- 新構成は以上で, Kron reduction (§7.3) には追加の言語構成は不要。

### 4.2 §8 (オンライン/時変) が意味論に要求するもの

1. **時間添字付きシステム行列**: `S : Fin N → (P ⊕ M ≃ₗᵢ P ⊕ M)` (公開 P と共通メモリ M は全ホライズン分を
   事前確保して固定。Kalman の失敗セクタも事前確保の direct sum に入る) と, 時刻ごとのクエリ
   `Q_j = ⊕_{a ∈ sched j} O_{a,j}` (未スケジュールは恒等)。query-before-work 規約 `W_j = S_j (I_P ⊕ Q_j)`。
2. **因果リフト W_N^td**: `Ŵ_j` (公開スロット j 上で W_j, 他スロットは恒等) の積。意味論は二時刻カーネル
   `K_N : (Fin N → P) →L (Fin N → P)` (下三角)。プレフィックス整合はリストの snoc に関する定理として述べる。
3. **二時刻クロック**: クロック層を **一般のブロックカーネル** `E : Fin N_out → Fin N_in → (P →L Q)` に対して
   定義する (`L_X(E) = Σ X_{oi} E_{oi}`, Thm 2.3/Lemma 2.4)。Toeplitz 場合は `c_n(X) = Σ_{o−i=n} X_{oi}` による系。
   論文の Lemma 2.4 は既にこの一般形なので追加コストはない。sketch の 4. (`W_N[G]`, `G̃_N = Σ c_n G_n`) は
   この系として得る。
4. **アクセスモデル (オンライン性)**: 意味論は固定された古典記録 ω を引数に取る (`∀ ω` で述べる)。
   「イベント j のステップは O_{·,j} のみ使い, 逆・過去オラクルを使わない」は回路構文上の述語 `IsOnline`
   として資源層に置く。入力クロックはストリーム前に準備, 出力クロックは読み出し時の記録に依存可, という
   **因果的クロック準備** はクロック分解に付く追加仮定 (Thm 8.2 後の注) で, nuclear-norm 条件とは別。
5. **解析変数の扱い**: z は依然としてオラクル使用回数を数えるが, オンラインでは伝達関数 F(z) を経由せず
   カーネル比較 `‖K_N − T_N[G]‖ ≤ η_N` (U8.a) で時不変の解析的クロック定理に接続する。従って Sec. 3 の解析的
   クロック整形は時不変のまま残し, オンライン側はカーネルレベルの摂動 (8.11)(8.12) と (8.14) で閉じる。
6. **確率・測定層**: Prop 8.8 と Thm 8.11 はコピーのテンソル積, 成功フラグ測定, trace distance を要する。
   core の module 意味論 (純粋に線形代数) とは分離し, `MQSP/Online/Copies.lean` 等の上位層に置く。

### 4.3 sketch の時不変 module は安く一般化できるか

**できる。推奨は「時変を基本, 時不変を特殊化」とする順序の入れ替え**。

- sketch の `Module` (system matrix S, 遅延 r_j) から, 遅延線 (巡回シフトバッファ) を含む 1 tick の
  ユニタリ `W(O) = S_buf (I ⊕ Q(O))` on `P ⊕ M`, `M = ⊕_j (Fin r_j ⊗ K j)` を定める関数 `Module.tick` を
  一つ用意すれば, `Module.lift N O := causalLift (fun _ => Module.tick O)` で Thm 2.2 のリフトが得られる。
- Prop 8.1 (一般の `causalLift`) を先に証明し, Thm 2.2 は「定数系列ならカーネルは Toeplitz で
  `H_{t,s} = G_{t−s}`」という補題 (`B D^{n−1} C = G_n`: 遅延付き実現のインパルス応答 = 多変数係数の遅延和)
  を加えるだけで従う。この補題は時不変版でも必要なので追加負担はほぼない。
- 必要な追加: (i) カーネル型 (二時刻) を意味論の第一級オブジェクトにすること, (ii) オラクル組を時刻添字付き
  `O : Fin N → ∀ a, K a →L K a` に拡げること (時不変は定数関数), (iii) promise を (記録, オラクル列) の組 ω 上に
  とること。いずれも型を一段一般化するだけで, 既存の steady-state (z=1) 意味論・multivariate 係数・Close 等の
  接続規則は時不変 module に対してそのまま残る (オンライン側では接続規則を各 tick の S_j に適用する:
  Kalman の各イベントは「直接クエリ module + 既知 junction」の Series)。
- 一般化しないもの: 伝達関数 F(z), group delay, 解析的クロック整形は時不変専用に留める。オンラインの
  時間方向の解析性 (Bernstein 楕円, E.2) は optional 層で別扱い。
- 注意点: (a) Ŵ_j を構成するには公開スロット j への埋め込み `(Fin N → P) ⊕ M` が必要で, PiLp 2 上の
  「1 成分だけに作用する」演算子の補題群を Core に用意する。(b) 上三角成分 X_{oi} (o<i) はカーネルが 0 でも
  クロック最適化 (核ノルム完備) に必要なので, クロック行列は正方 `Fin N × Fin N` 全体で持つ。
  (c) 事前確保メモリ M は horizon 依存なので, `causalLift` は M を引数に取り N に依存してよい設計にする。
