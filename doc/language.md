# lean-mqsp 言語の使い方

- 対象読者: mQSP / QSVT に基づく量子アルゴリズムを operator-level で書き，その定理を Lean で得たい人．
- 前提: block encoding と mQSP の module（unitary junction，フィードバック，transfer function）の概念．
- 対応モジュール: `MQSP/Lang/Prog.lean`（言語），`MQSP/Module/`（意味論），`MQSP/Compile/`（回路），
  `MQSP/Clock/`（近似），`MQSP/Resource/`（資源）．設計の背景は [design.md](design.md)．

## 1. プログラム

```lean
import MQSP
open MQSP MQSP.Prog
```

プログラム `Prog P pf` は public 空間 `P` とポート族 `pf : PortFamily`（露出する oracle ポートの
添字型 `pf.ι` と各ポートの空間 `pf.K j`）で型付けされます．

| 構文 | 意味（mQSP §5.2） |
|---|---|
| `prim M` | 生の unitary junction `M : Junction P L pf.K`（Prop 5.1）|
| `query E` | oracle `U : E →L[ℂ] E` の直接問い合わせ（`S = swap`）|
| `cayley E` | Cayley module（self-inverse block encoding → Cayley 変換）|
| `chain cd` | 有限 query 回路 `V_d O_{d−1} ⋯ O_0 V_0`（QSP 位相列はこれ）|
| `p ;; q` | Series（`p` のあと `q`）|
| `wireBefore V hV p`, `wireAfter V hV p` | 既知ユニタリを前/後に（記法 `V ◁[hV] p`, `p ▷[hV] V`）|
| `p ⊕ₚ q` | DirectSum（直交する分岐）|
| `spectator n p` | レジスタ `Fin n` をテンソル |
| `inverse p` | 逆ネットワーク（`S†`，oracle は `Oⱼ†`）|
| `p[j ≔ q]` | Substitute: `p` のポート `j` の oracle を `q` で実装（`q` の public 空間は `pf.K j`）|

ポート族は `PortFamily.one E`（1 ポート），`pf₁.sum pf₂`（Series/DirectSum/Substitute の結果），
`pf.reg n`（spectator），`PortFamily.chain H d` で作られます．

## 2. 意味論

oracle 組 `O : Oracles pf`（各ポートに作用素）に対し

- `steady p O : P →L[ℂ] P` — 定常値（transfer function の `z = 1` での値）．`IsRegular p O` と oracle の
  ユニタリ性の下でユニタリ（`isUnitary_steady`）．
- `weight p O j ψ : ℝ` — ポート `j` の catalyst 重み（Las Vegas クエリ重み）．
- `G p O n` — impulse response，`lift p O N` — horizon `N` の unitary Toeplitz lift，
  `queries p N j = ⌊(N−1)/delay p j⌋` — ポート `j` の呼び出し回数．

合成的意味論（`MQSP/Lang/Prog.lean`）:

```lean
steady (p ;; q) O = steady q O.right ∘L steady p O.left           -- steady_series
steady (p ⊕ₚ q) O = block (steady p O.left) 0 0 (steady q O.right)  -- steady_dsum
steady (spectator n p) (reg n O) = Reg.map (steady p O)             -- steady_spectator
steady (inverse p) (inv' O) = (steady p O)†                          -- steady_inverse
steady (p[j ≔ q]) O = steady p (update O.left j (steady q O.right)) -- steady_subst
weight (p ;; q) O (inr j) ψ = weight q O.right j (steady p O.left ψ) -- weight_series_inr（thrifty）
```

## 3. 回路と資源

- `Prog.toeplitz_block`: `lift p O N` の public ブロック `(o,i)` は `G p O (o − i)`（`i ≤ o`）．
- clock（`MQSP/Compile/Clock.lean`）: clock 状態 `cin, cout` で `1 ⊗ lift` を挟むと
  `Σ_n c_n(X) G_n` の encoding（`isEncodingOf_quditize`）．
- **uniform clock**（`MQSP/Clock/Uniform.lean`）: unit delay の regular な module に対し，horizon `N` の
  lift と箱型 clock は定常値から `‖Γ‖/√N` 以内の作用素を正規化 1 で符号化（`isEncodingOf_uniform`）．
- endpoint clock（`MQSP/Compile/Endpoint.lean`）: impulse response が遅延 `T` に集中する module
  （chain）は厳密に符号化．
- 資源（`MQSP/Resource/Cost.lean`）: `CostModel`（ポート→oracle 型，コスト）に対する
  重み付きクエリコスト `weightedCost = Σⱼ Cⱼ ⌊(N−1)/rⱼ⌋`．

## 4. QSVT を書く

位相列 `Φ : List ℝ`（時間順）と block encoding `U`，射影 `Pr, Pr'` に対し

```lean
QSVT.qsp Pr Pr' hPr hPr' Φ : Prog H (PortFamily.chain H Φ.length)   -- 位相列 module（chain）
QSVT.qsp_steady : steady (qsp …) (oracles (chainOracles U _)) = UΦ U Pr Pr' Φ
QSVT.proj_UΦ_proj_odd : Pr' ∘L UΦ … ∘L Pr = enc U Pr Pr' ∘L aeval (enc† enc) (pqΦ Φ).1
```

`pqΦ Φ : ℂ[X] × ℂ[X]` は `y = x²` に関する QSP 多項式対で，実現される多項式は
`P_Φ(x) = x^{|Φ| mod 2} p_Φ(x²)`．`(U_Φ + U_{−Φ})/2` は `Re P_Φ` を実現し（`proj_average_proj_odd`），
`|+⟩` フラグの DirectSum として encoding になります（`isEncodingOf_average`）．
Hermitian な `A` では `Core/Spectral.lean` の spectral mapping で `‖P(A) − f(A)‖ ≤ ε` が得られます．

## 5. 近似多項式

`MQSP/Poly/`: parity（`IsEven`/`IsOdd`），`BoundedOn`，`ApproxOn`，Chebyshev，
Weierstrass による存在定理（`exists_even_approx`, `exists_odd_approx`, `exists_sign_approx`,
`exists_amplifier`）．次数の定量評価は別途．

## 6. Coherent estimation の primitive

- `CPE.phaseSignal U = 1 ⊕ U` と `|+⟩` ブロック `(1+U)/2`；固有ベクトル `Uψ = e^{iθ}ψ` 上で
  `A†A = cos²(θ/2)`，偶位相列の QSVT は `p_Φ(cos²(θ/2))` を返す（`proj_UΦ_plus_eigen`）．
- `CPE.ApproxImpl ε M W S`（clean ancilla のベクトルレベル仕様），stitching `ApproxImpl.comp`，
  uncompute `ApproxImpl.uncompute`．

## 7. 信頼境界

Lean の定理（意味論・合成則・lift の正しさ・clock 誤差・資源）は信頼されます．
`describe`/`numPorts` は計算可能ですが，意味論は noncomputable（`#eval` 不可，定理で使う）．
公理は `propext`, `Classical.choice`, `Quot.sound` のみ（`test/` で監査）．
