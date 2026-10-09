# PROGRESS

進捗ログ（新しいものを上に）．計画は [dev/plan.md](dev/plan.md)，設計は [doc/design.md](doc/design.md)，
仕様 ID は [dev/formal-spec.md](dev/formal-spec.md)，論文調査は [dev/inventory/](dev/inventory/) を参照．

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
