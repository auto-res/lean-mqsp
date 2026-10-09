# lean-mqsp 言語設計 (v2)

mQSP (Low, arXiv:2610.01125) を出発点に，量子アルゴリズムを operator-level で記述し，
Lean 4 で正しさ・近似誤差・oracle ごとのクエリ複雑さを合成的に証明するための
量子プログラミング言語と意味論の設計をまとめる．QSVT (GSLW, arXiv:1806.01838) と
coherent phase estimation (Rall, arXiv:2103.09717) はこの言語の上で記述する．

対応する Lean の名前を `monospace` で示す．仕様 ID（MOD-1 など）は `dev/formal-spec.md` に対応する．

---

## 1. 設計原理

1. **プログラム = module（unitary junction）のネットワーク**．mQSP の中心概念は
   「既知のユニタリ system matrix `S = [[A,B],[C,D]]` を public 空間 `P` と private 空間 `L`
   の直和に置き，private の各 port に oracle `O_j` をフィードバックで接続する」ことであり
   (mQSP Eq. (1.1)–(1.3), Prop 5.1)，これが言語の唯一の primitive である．
   位相列・LCU・振幅増幅・位相推定の回路はすべて junction の接続として現れる．
2. **意味論は 4 層**．(i) steady state（z = 1，代数）, (ii) impulse response（時間領域），
   (iii) compile（Toeplitz lift と clock），(iv) approximation / resource．
   接続規則ごとに各層の合成定理を証明し，上位の定理は接続規則の定理の合成で得る．
3. **oracle は promise 付きの自由変数**．module は oracle 組 `O : ∀ j, K j →L[ℂ] K j` の関数として
   意味を持ち，定理は promise（ユニタリ性，block-encoding 性，スペクトル条件…）を仮定として量化する．
   これにより「一つの有限回路が promise 全体で一様に正しい」ことがそのまま Lean の定理になる．
4. **oracle の表現は block encoding**．`Be[A/λ]` は signal 射影 `Π_in, Π_out` を持つユニタリ
   (mQSP Eq. (1.16), GSLW Def 43)．Hermitian 信号・特異値信号・状態準備は，それぞれ
   Hermitian dilation，ReflectionWalk，PreparationQuery という *module* で同じ形式に落とす（§5.1）．
5. **低レベルは導出物**．qubit，ゲート列，QSP 位相，補助 wiring はユーザーが書くものではなく，
   compile 層（Toeplitz lift・clock・routing）の定理が生成・勘定する．

---

## 2. 基本語彙（`MQSP.Core`）

- Hilbert 空間: 有限次元複素内積空間の束 `HSpace E`（CORE-1）．作用素は `E →L[ℂ] F`，随伴 `A†`，
  `IsUnitary`, `IsIsometry`, `IsProj`（直交射影），反射 `reflection P = 2P − 1`．
- 直和 `P ⊕ₕ L := WithLp 2 (P × L)`（CORE-2）: `inl, inr, fst, snd` と 2×2 ブロック作用素
  `block A B C D`（合成・随伴・外延性・分解 `eq_block`）．
- ポート直和 `PiSum K := PiLp 2 K`（CORE-3）と対角 `diag O = ⊕ⱼ Oⱼ`．
- レジスタ `Reg N E := PiLp 2 (fun _ : Fin N => E)`（「`Fin N ⊗ E`」）．テンソル積は使わず，
  有限レジスタとの積は直和（`N` 個のコピー）で表す．clock レジスタ・遅延バッファ・補助 qubit は
  すべてこの形．
- 恒等拡張 `extendR L₂ S`, `extendL L₁ S`（CORE-4）: `S ⊕ 1` を `P ⊕ₕ (L₁ ⊕ₕ L₂)` 上に置く．

---

## 3. Primitive: unitary junction（`MQSP.Module`）

```
structure Ports (L) (K : ι → Type) :      -- private 空間のポート分解（coisometry の族）
  π : ∀ j, L →L[ℂ] K j ; π j (π j)† = 1 ; π i (π j)† = 0 (i ≠ j) ; Σ (π j)† π j = 1
structure Junction (P L) (K : ι → Type) : -- MOD-1
  S : P ⊕ₕ L →L[ℂ] P ⊕ₕ L ; isUnitary_S ; ports : Ports L K ; delay : ι → ℕ ; 1 ≤ delay j
```

実装上の注記（v2）: 定常状態は regular（`1 − DQ` 可逆）版 `catalyst/steady` に加えて，
**regular 仮定なしの最小ノルム版** `catalyst₀/steady₀`（`Module/Steady.lean`）を持つ．有限次元で `S`, `Q` が
ユニタリなら `ran C ⊆ ran(1 − DQ)` が成り立ち，定常解は常に存在し，`steady₀` は常にユニタリである
（調査 `dev/inventory/mqsp-core.md` §5.2 G2 の指摘）．regular なら両者は一致する．

- `ι` はポートの添字（有限型），`K j` は port `j` の oracle 空間．同じ oracle を異なるレートで
  問い合わせる場合は別ポートにする．ポートの「コピー」(`Icopy ⊗ Oⱼ`) はアドレス付き直和であり
  1 回の制御付き呼び出しなので，`K j` の中に含めてよい（クエリ数はポート呼び出しで数える）．
- `L` を `PiSum K` に固定せず `Ports` で抽象化した理由: 接続規則（Series など）の private 空間が
  `L₁ ⊕ₕ L₂` という素直な直和になり，`PiLp` の添字付け替えが不要になる．`Ports.pi` が標準例．
- フィードバック `Q O = Σⱼ (π j)† Oⱼ (π j)`（mQSP Eq. (2.2)）．oracle 組 `O : OracleTuple K`．
- oracle の種類（promise）は `OracleTuple` 上の述語として別に与える: ユニタリ，self-inverse，
  `IsBlockEncoding Π_in Π_out A λ`，Hermitian，スペクトル条件など（`MQSP.Core.BlockEncoding`）．

### 3.1 層 (i): steady state（MOD-2）

- regular: `IsUnit (1 − D Q)`．catalyst `Γ := (1 − D Q)⁻¹ C`，transfer value
  `F := A + B Q Γ`（mQSP Eq. (1.3)）．定常方程式 `S(ψ ⊕ QΓψ) = Fψ ⊕ Γψ`（Eq. 2.7）と
  ノルム保存 (2.10) から **`F` はユニタリ**（`isUnitary_steady`; Prop 5.1 / Thm 2.1）．
- ポートごとの catalyst weight `W_j(ψ) = ‖π_j Γ ψ‖²`（Eq. 2.8）．`Σ_j W_j = ‖Γψ‖²`．
- この層が「理想的な module の正しさ」を担う: 例えば `HamSim t (Be H λ)` の steady value が
  `e^{-itH}` であること．

### 3.2 層 (ii): impulse response（時間領域；MOD-3，`Module/Impulse.lean`）

- unit delay の再帰 (mQSP Eq. 2.20): `y_k = A u_k + B O g_{k−1}`, `g_k = C u_k + D O g_{k−1}`，
  一般の遅延は port `j` の読み出しが `k − r_j` 時刻の書き込み（1 回の oracle 呼び出し後）になる．
  impulse response `G_n : P →L[ℂ] P`（`u = δ₀`）を時間領域の再帰で定義する．
- 多変数係数 `F_n`（`n : ι → ℕ`，Eq. 2.3）はポートごとの呼び出し回数で細分化した経路和で，
  `G_n = Σ_{⟨r,m⟩=n} F_m`．生成関数 `F(z;O)`, `G(z) = Σ G_n zⁿ` は解析層でのみ使う．
- 群遅延作用素 `W = G† G′ = Σ_j r_j Γ_j†Γ_j`（Eq. 1.13/2.13）は (i) の量で表せる．

### 3.3 層 (iii): compile（COMP-C，`Compile/Lift.lean`, `Compile/Clock.lean`, `Compile/Endpoint.lean`）

- **回路 IR**: 時刻付きの既知ユニタリと「ポート `j` への制御付き呼び出し」の列．
  クエリ数 `q_j` は IR 上の計算可能な関数．
- **unitary Toeplitz lift** `W_N[G]`（Thm 2.2）: 空間 `H_{N,r} = Reg N P ⊕ₕ ⊕ⱼ Reg (r j) (K j)`，
  ステップ `k` で埋め込み `J_k`（clock `|k⟩`，port バッファ `|k mod r_j⟩`）を通して `S` を適用，
  `r_j ∣ k` のときポート `j` の全バッファに `Oⱼ` を 1 回適用．定理: public ブロックは
  Toeplitz `T_N[G]_{o,i} = G_{o−i}`，`q_j = ⌊(N−1)/r_j⌋`，`T_N[G]` は縮小 (Eq. 2.26)．
  一般の時変系列（§8 の causal lift, Prop 8.1）を先に定義し，定数系列の場合として得る．
- **clock**（Thm 2.3 の構成方向，Lemma 2.4）: clock 係数行列 `X = Σ_ℓ s_ℓ a_ℓ b_ℓ†`（明示的因数分解，
  `Σ s_ℓ ≤ α`）から入出力 clock 状態を作り，`Be[ L_X(T_N[G]) / α ]`，Toeplitz なら
  `L_X(T_N[G]) = Σ_n c_n(X) G_n = G̃_N`．核ノルム最小性（only-if）は optional．
- 結果の形: 「プログラム `p` と horizon/clock パラメータから，`Be[G̃_N/α]` を実装する有限回路と
  クエリ数 `q_j` が得られる」が定理になる．

### 3.4 層 (iv): approximation と resource（CLK-*, RES-*；`Clock/`, `Resource/`）

実装済み（v2）: transient 恒等式と S1（`Clock/Transient.lean`），箱型 clock（`Clock/Flat.lean`），
uniform clock の end-to-end 定理 `isEncodingOf_uniform`（mQSP Thm 3.2: 誤差 `‖Γ‖/√N`，正規化 1；`Clock/Uniform.lean`），
生成関数と Cauchy 裾評価（`Clock/Analytic.lean`），資源勘定（`Resource/Cost.lean`），
正規化・条件付き状態・OAA（`Resource/Approx.lean`），重み付き遅延配分（`Resource/Allocation.lean`）．
解析的 clock shaping（Thm 3.9）は未着手．

- transient 恒等式 (Eq. 1.12): `G†(G − G̃_N) = (1−c₀) I + Σ (c_n − c_{n+1}) K_n`，
  `K_n = G†(G − Σ_{k≤n} G_k)`．
- uniform clock（Thm 3.2/Lemma 3.3），flat clock（Lemma 3.5），smoothed window（Lemma 3.6）．
- 解析的 clock shaping（Thm 3.9）は「係数の裾の評価 ⟹ clock 誤差」と「解析的増大度 ⟹ 裾の評価
  （Cauchy 評価）」に分けて形式化する．
- resource（Def A.1）: ポートごとのコスト `C_j`，重み付きクエリコスト `⟨C,q⟩`，補助次元，
  誤差予算 (Eq. A.13)．OAA（Lemma A.4）は正規化 2 の block encoding をユニタリに変換する module．

---

## 4. 接続規則（`MQSP.Compose`，mQSP §5.2）

| 規則 | 新しい (public, private, ports) | system matrix | steady / catalyst / weight |
|---|---|---|---|
| Wire V（前/後） | (P, L, ι) | `S (V ⊕ 1)` / `(V ⊕ 1) S` | `F V` / `V F`；`Γ V` / `Γ` |
| Series | (P, L₁ ⊕ₕ L₂, ι₁ ⊕ ι₂) | `(S₂ ⊕ 1)(S₁ ⊕ 1)` | `F₂F₁`；`Γ₁ ⊕ Γ₂F₁`；`W₁ + F₁†W₂F₁` (5.15) |
| DirectSum | (P₁ ⊕ₕ P₂, L₁ ⊕ₕ L₂, ι₁ ⊕ ι₂) | `S₁ ⊕ S₂` | `F₁ ⊕ F₂`；`W₁ ⊕ W₂` |
| Spectator R | (Reg N P, Reg N L, ι) | `1_R ⊗ S` | `1 ⊗ F` |
| Close（E を wV で閉じる） | (P, E ⊕ₕ L, ι) | 既知の基底変換 | `F_pp + F_pe V (1 − F_ee V)⁻¹ F_ep`（正則性仮定） |
| Substitute（port j に module B） | (P_A, L_A ⊕ₕ L_B, (ι_A∖{j}) ⊕ ι_B) | `(S_A ⊕ 1)(1 ⊕ S_B)` | `A_A + B_A F_B (1 − D_A F_B)⁻¹ C_A` |
| Delay r | 同じ | 同じ（delay 変更） | 同じ；lift のクエリ数が `⌊(N−1)/r⌋` に |
| Inverse | 同じ | `S†`，oracle `O†` | `F†` |
| Project（Π_in, Π_out） | block encoding の抽出 | — | `Π_out F Π_in` |

各規則について層 (i)–(iv) の合成定理を証明する．v2 時点で Series / Wire / DirectSum / Spectator / Inverse /
Substitute / Delay / Project(LCU) の層 (i) の合成定理（定常値・catalyst・重み）が証明済み（`MQSP/Compose/`）．
Close は未着手（Substitute と WeightedCayley の内部で必要な分は個別に証明）．

---

## 5. Library modules（`MQSP.Modules`，mQSP §5.1/5.3）

| module | 入力 oracle | `S` | transfer `F(z;x)` | 役割 |
|---|---|---|---|---|
| Query | 任意ユニタリ O | swap | `zO` | 直接問い合わせ |
| AP1_a | 位相 x=e^{iφ} | 2×2 回転 | `(zx−a)/(1−azx)` | 1 次 all-pass |
| Cayley | self-inverse Be[H/λ] | 3×3 (1.24) | `z(z−ix)/(1+ixz)`，値 `e^{−2i arctan x}` | Hermitian 信号の位相化 |
| WeightedCayley | Be[Hⱼ/λⱼ] の族 | Lemma 5.2 | `(I−M)(I+M)⁻¹`, `M(1)=iΣHⱼ/Λ` | 非可換和 |
| Exp_τ | 内部 module | (1.45) | `e^{−τ(1−w)/(1+w)}` | 位相の線形化 |
| HamSim_t = Exp∘Cayley | Be[H/λ] | 融合 (5.36) | `e^{−itλx}` | Hamiltonian simulation |
| FPAA tap | 準備 oracle A, A† | (1.38)/(5.24) | BiQuad all-pass | 固定点振幅増幅 |
| Sign lattice | self-inverse Be[A] | Schur lattice (5.30) | `tanh(L artanh x) → sgn x` | 符号関数/閾値 |
| HermitianDilation, ReflectionWalk, PreparationQuery | Be[A/λ], U | (5.12)–(5.14) | — | 信号の正規化 |
| Reciprocal_d | Hermitian 信号 | shifted Cayley の列 | `u^{2d−1}/(1+u^{2d}) ≈ 1/u` | 線形方程式 |

QSVT の位相列 `Φ` に対する module は `qsp Φ U := Series_k (Wire (e^{iφ_k(2Π−1)}) ; Query U)`
（`U` と `U†` を交互に）で，`F(z) = z^d U_Φ`，catalyst weight `d`．

---

## 6. 表面言語（`MQSP.Lang`，実装済み v2）

```
inductive Prog : (P : Type u) → [HSpace P] → PortFamily → Type (u+1)
| prim (M : Junction P L pf.K)                 -- 生の primitive（Prop 5.1）；library modules はここから
| series (p : Prog P pf₁) (q : Prog P pf₂) : Prog P (pf₁.sum pf₂)          -- p ;; q
| wireBefore / wireAfter (V) (hV) (p)                                      -- V ◁[hV] p, p ▷[hV] V
| dsum (p : Prog P₁ pf₁) (q : Prog P₂ pf₂) : Prog (P₁ ⊕ₕ P₂) (pf₁.sum pf₂)  -- p ⊕ₚ q
| spectator (n) (p) : Prog (Reg n P) (pf.reg n)
| inverse (p)
| subst (p : Prog P pf) (j : pf.ι) (q : Prog (pf.K j) pf') : Prog P (pf.sum pf')  -- p ⇐[j] q
```

プログラムは public 空間とポート族 `pf`（露出 oracle ポートの添字型と各ポート空間）で型付けされ，
private 空間は `denote : Prog P pf → Den P pf` が計算する（Σ 型）．`steady/weight/G/lift/queries` は `denote` 経由で定義され，
接続規則ごとの合成的意味論（`steady_series` など）と end-to-end の compile 定理（`Prog.isEncodingOf_uniform`）を持つ．
`describe`/`numPorts` は計算可能，`#mqsp_info p` はネットワーク構造とポート数を表示する（`Lang/Info.lean`）．
library modules: `query`, `cayley`, `chain`（有限 query 回路；QSP 位相列は `QSVT.qsp`）．

---

## 7. QSVT を特殊ケースとして（`MQSP.QSVT`）

- block encoding `U` と射影 `Π, Π̃`，位相列 `Φ`（長さ d）に対し `qsp Φ U` は上記の Series module．
  各ステップは `D = 0` なので regular で，steady value は `U_Φ`（Query の steady は `O`）．
- **QSVT 定理（GSLW Thm 17）**: `Π̃ U_Φ Π = P_Φ^{(SV)}(A)`．これは `qsp Φ U` の steady value の
  2 次元不変部分空間上の計算（qubitization = 単一 oracle の spectral mapping 原理）．
  mQSP の言葉では「一つの Hermitian/特異値信号については eigenspace でスカラー式を検証すれば
  よい」(§5 冒頭)．
- **compile**: horizon `d+1`，endpoint clock `X = |d⟩⟨0|`（`α = 1`）で `qsp Φ U` を lift すると，
  public ブロックの `(d,0)` 成分が `U_Φ` そのもの（mQSP Thm 4.4/4.8 の構成）．すなわち QSVT 回路は
  mQSP の quditization の endpoint clock の場合である．
- block-encoding 算術: LCU = DirectSum + Wire(準備) + Project（GSLW Lemma 52），
  積 = Series + Project（Lemma 53），実多項式 = `qsp Φ` と `qsp (−Φ)` の DirectSum + Project（Cor 18）．
- 多項式近似（GSLW §5.2）は言語非依存の `MQSP.Poly` に置く（parity，sup norm，Chebyshev，
  sign/threshold/exp/inverse の近似定理）．

## 8. Coherent phase estimation（`MQSP.CPE`）

- 位相信号の block encoding（`U` と `U†` の LCU で `cos`/`sin`），エネルギー信号（Be[H] から直接），
  1 ビット抽出（符号/閾値多項式の QSVT = `qsp`），ビット列への coherent な書き込み（補助レジスタ
  = `Reg` と Series），振幅増幅（FPAA module / singular value amplification），振幅推定．
- mQSP/QSVT の一般定理から導ける部分（QSVT 定理，LCU，近似多項式，FPAA）は共通ライブラリを使い，
  coherent iteration の確率勘定・rounding promise・uncomputation など固有の primitive のみ新規に形式化．

## 9. 証明を合成的にするための型・IR の要点

- **ポートの抽象化**（`Ports`）により接続規則の private 空間が自然な直和になる．
- **regularity は単射性**（有限次元）で合成し，catalyst は不動点方程式の一意解として特徴付ける．
  これで Series/Substitute/Close の catalyst 公式が「候補を代入して検証」で証明できる．
- **impulse response と lift** は時刻付きの埋め込み `J k`（clock `|k⟩`，slot `k mod rⱼ`）と周期スケジュールで定義し，
  Toeplitz ブロックは時刻帰納法で証明した（時変系列への一般化は将来課題）．
- **clock は明示的因数分解を入力**とし，SVD/核ノルムの存在定理に依存しない．
- **解析層は係数列の評価に還元**し，複素解析（Cauchy 評価）は 1 箇所に隔離する．
- **oracle promise は述語**で，定理は `∀ O, promise O → …` の形；promise の合成（Series の左右の
  oracle 組への制限 `O.left`, `O.right`）も述語の合成．
