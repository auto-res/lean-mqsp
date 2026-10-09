# QSP 合成方向（QSVT-2）の lean-qsvt からの port メモ

lean-qsvt（MIT, shosonoda, 同一 Lean/Mathlib v4.34.1）の `QSVT/QSP/*` と
`QSVT/Polynomial/{Parity,SqrtPart}` を `MQSP/QSP/`（namespace `MQSP.QSP`）へ移植し，
橋渡しを `MQSP/QSVT/Phases.lean`（namespace `MQSP.QSVT`）に置いた．全ファイル sorry なし，
公理は `propext, Classical.choice, Quot.sound` のみ．

## ファイル対応

| MQSP/QSP/ | lean-qsvt 元 | 備考 |
|---|---|---|
| `Parity.lean` | `Polynomial/Parity.lean` (+ `QSP/PolyW.lean` の `HasParity.one_sub_X_sq_mul`, `coeff_eq_zero_of_odd_add`) | ℂ[X] の `IsEven/IsOdd/HasParity`（`MQSP.Poly.IsEven` は ℝ[X] 版で別物） |
| `SqrtPart.lean` | `Polynomial/SqrtPart.lean` | `evenRoot/oddRoot`, `isEven_iff_exists_comp_X_sq` |
| `Conventions.lean` | `QSP/Conventions.lean` | `Rref, phaseZ, seqR, Wrot, seqW` |
| `Poly.lean` | `QSP/Poly.lean` (+ `PolyW.lean` の `coeff_conjP` 等) | `qspPoly, qspPoly4, conjP, negX` |
| `Structure.lean` | `QSP/Structure.lean` | `seqR_eval`, 次数・パリティ・`norm_identity`, `qspPoly_neg` |
| `PolyW.lean` | `QSP/PolyW.lean` | `stepW, qspPolyW, seqW_eval, qspPolyW_unit` |
| `Conversion.lean` | `QSP/Conversion.lean` | GSLW Cor 8: `Wrot_eq_Rref`, `cor8Phases`, `seqW_apply_zero_zero_eq` |
| `Chebyshev.lean` | `QSP/Chebyshev.lean` | GSLW Lemma 9: `chebPhases`, `seqR_chebPhases` |
| `Endpoints.lean` | `QSP/Endpoints.lean` | QSP-5（x = ±1, 0 の値） |
| `Perturb.lean` | `QSP/Perturb.lean` | QSP-6（位相摂動 `‖seqR Φ - seqR Φ'‖ ≤ Σ|φ_j - φ'_j|`） |
| `Existence.lean` | `QSP/Existence.lean` を **反射規約に書き直し** | `stepR/unstepR` による次数下げ帰納法を `qspPoly` 上で直接実行（W 規約を経由しない） |
| `ExistenceW.lean` | `QSP/Existence.lean`（W 部分）+ `Complementary.lean` の `exists_phases_real` | `exists_phases_W`（旧名 `exists_phases`），`exists_phases_R_of_W`（旧 `exists_phases_R`，Cor 8 経由），`exists_phases_W_real` |
| `Complementary.lean` | `QSP/Complementary.lean` | Lemma 6 `exists_sumsq_decomposition`，Thm 5 `exists_complement`，`exists_phases_R_poly_real`，`exists_phases_R_real`；`rePoly` は `MQSP.QSVT.rePoly` |

未移植: `QSVT/Polynomial/{SupNorm,Chebyshev,ChebCoeff}`（Chebyshev 級数・証明書用で，
QSP 合成の依存関係に入っていない）．

## 規約の対応（位相変換なし，順序反転のみ）

スカラー場合 `H = ℂ², Pr = Pr' = |0⟩⟨0|, U = R(x)` では `e^{iφ(2Pr-1)} = e^{iφσ_z}`,
`U† = U` なので `U_Φ = seqR Φ.reverse x`（`seqR` のリスト先頭が最も新しい因子）．
`Shape` から，`k` ステップ後の `(p, q)`（`y = x²`）に対応する `qspPoly` の対は

- `k` 偶数: `(p(X²), X q(X²))`，`k` 奇数: `(X p(X²), q(X²))`（`liftPQ`）

で，`liftPQ (k+1) (pqStep k φ st) = stepR φ (liftPQ k st)`（同じ位相 φ）．よって
`qspPoly Φ.reverse = liftPQ |Φ| (pqΦ Φ)`（`qspPoly_reverse`），
`(seqR Φ.reverse x)₀₀ = x^{|Φ| mod 2} p_Φ(x²)`．W 規約の位相 `(φ₀; Φ')` からは
`(cor8Phases φ₀ Φ').reverse`（GSLW Cor 8，`-π/2` シフト）が我々の時間順位相列．

## 主定理

`MQSP.QSVT.exists_phases`：指定文に **`(hn : 1 ≤ n)` を追加**．n = 0 では Φ = [] しかなく
`p_Φ = 1` なので偽（`not_exists_phases_zero` が P = 1/2 で反例を形式化）．GSLW Cor 10 も n ≥ 1．
系: `exists_phases_eval`, `exists_phases_seqR`, `exists_phases_proj_average_proj_odd/even`
（Cor 18 と合わせた演算子形），`qspScalar_chebPhases_reverse`, `qspScalar_cor8Phases_reverse`,
`norm_eval_qspScalar_le_one`．

## 残り / 注意

- `MQSP.lean` に `import MQSP.QSVT.Phases`, `MQSP.QSP.Endpoints`, `MQSP.QSP.Perturb` の追加が必要
  （既存ファイルは編集していない）．テスト（`#print axioms` ガード）も未追加．
- namespace `MQSP` 内では `MQSP.one_comp`（`Core/HSpace.lean`，CLM 用）が `Polynomial.one_comp` を
  隠す．多項式では `Polynomial.one_comp` と明示すること．
