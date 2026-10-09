/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.PiSum

/-!
# Junctions (mQSP modules) and their steady-state semantics (MOD-1, MOD-2)

An mQSP module (mQSP §1 Eq. (1.1), §5.1 Eq. (5.1), Prop 5.1) is a *unitary junction*: a known
unitary system matrix `S = [[A, B], [C, D]]` on `P ⊕ₕ L` (public space `P`, private space `L`),
where the private space is decomposed into oracle ports `L ≅ ⊕ⱼ K j` (a `Ports` structure:
coisometries `π j : L → K j` with `π j (π j)† = 1`, `π i (π j)† = 0` for `i ≠ j`,
`∑ⱼ (π j)† π j = 1`), together with integer port delays `r j ≥ 1`. The oracle tuple
`O : ∀ j, K j →L[ℂ] K j` is substituted into the private ports through the feedback operation
`Q = ⊕ⱼ O j = ∑ⱼ (π j)† (O j) (π j)` (Eq. (2.2)).

Keeping `L` abstract (instead of fixing `L = PiSum K`) makes the connection rules of §5.2
(series, direct sum, substitution, ...) ordinary direct sums `L₁ ⊕ₕ L₂` without reindexing;
`PiSum K` with its projections is the canonical instance `Ports.pi`.

## Steady-state semantics (z = 1)

* `catalyst O = (1 - D Q)⁻¹ C` (the catalyst operator `Γ(1)`, Eq. (1.3a)), defined when the
  closed loop is *regular* (`1 - D Q` invertible);
* `steady O = A + B Q (catalyst O)` (the transfer value `F(1) = G`, Eq. (1.3b));
* `weight O j ψ = ‖π j (Γ ψ)‖²` (the per-port catalyst weight, Eq. (2.8)).

The steady-state equation `S (ψ ⊕ Q Γ ψ) = F ψ ⊕ Γ ψ` (Eq. (2.7)) and unitarity of `S` give
that `F` is unitary (Prop 5.1 / Thm 2.1 at `z = 1`).
-/

namespace MQSP

universe u v w x

open scoped InnerProductSpace
open Finset

/-- MOD-1. An oracle tuple: one operator per port. -/
abbrev OracleTuple {ι : Type u} (K : ι → Type v) [∀ i, HSpace (K i)] : Type max u v :=
  ∀ i, K i →L[ℂ] K i

/-- Every port carries a unitary. -/
def OracleTuple.IsUnitary {ι : Type u} {K : ι → Type v} [∀ i, HSpace (K i)]
    (O : OracleTuple K) : Prop :=
  ∀ i, MQSP.IsUnitary (O i)

/-- MOD-1. A decomposition of the private space `L` into orthogonal ports `K i`:
coisometries `π i : L → K i` whose adjoints are orthogonal isometries summing to the identity. -/
structure Ports (L : Type v) [HSpace L] {ι : Type u} [Fintype ι] (K : ι → Type w)
    [∀ i, HSpace (K i)] where
  /-- Projection onto port `i`. -/
  π : ∀ i, L →L[ℂ] K i
  /-- `π i (π i)† = 1`. -/
  π_comp_adj_self : ∀ i, π i ∘L (π i)† = 1
  /-- `π i (π j)† = 0` for `i ≠ j`. -/
  π_comp_adj_ne : ∀ i j, i ≠ j → π i ∘L (π j)† = 0
  /-- `∑ᵢ (π i)† π i = 1`. -/
  sum_adj_comp : ∑ i, (π i)† ∘L π i = 1

namespace Ports

variable {L : Type v} [HSpace L] {ι : Type u} [Fintype ι] {K : ι → Type w} [∀ i, HSpace (K i)]
variable (ps : Ports L K)

theorem π_adj_apply_self (i : ι) (x : K i) : ps.π i ((ps.π i)† x) = x := by
  have := congrArg (fun T : K i →L[ℂ] K i => T x) (ps.π_comp_adj_self i)
  simpa using this

theorem π_adj_apply_ne {i j : ι} (h : i ≠ j) (x : K j) : ps.π i ((ps.π j)† x) = 0 := by
  have := congrArg (fun T : K j →L[ℂ] K i => T x) (ps.π_comp_adj_ne i j h)
  simpa using this

theorem sum_adj_apply (v : L) : ∑ i, (ps.π i)† (ps.π i v) = v := by
  have := congrArg (fun T : L →L[ℂ] L => T v) ps.sum_adj_comp
  simpa [_root_.sum_apply] using this

/-- `‖v‖² = ∑ᵢ ‖π i v‖²`. -/
theorem norm_sq_eq (v : L) : ‖v‖ ^ 2 = ∑ i, ‖ps.π i v‖ ^ 2 := by
  have h1 : (⟪v, v⟫_ℂ) = ∑ i, ⟪ps.π i v, ps.π i v⟫_ℂ := by
    calc ⟪v, v⟫_ℂ = ⟪∑ i, (ps.π i)† (ps.π i v), v⟫_ℂ := by rw [ps.sum_adj_apply v]
      _ = ∑ i, ⟪(ps.π i)† (ps.π i v), v⟫_ℂ := sum_inner _ _ _
      _ = ∑ i, ⟪ps.π i v, ps.π i v⟫_ℂ :=
          Finset.sum_congr rfl (fun i _ => ContinuousLinearMap.adjoint_inner_left _ _ _)
  simp only [inner_self_eq_norm_sq_to_K] at h1
  exact_mod_cast h1

theorem norm_π_le (i : ι) (v : L) : ‖ps.π i v‖ ≤ ‖v‖ := by
  rw [← abs_norm, ← abs_norm v, ← sq_le_sq, ps.norm_sq_eq]
  exact Finset.single_le_sum (f := fun j => ‖ps.π j v‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem isIsometry_adj_π (i : ι) : IsIsometry ((ps.π i)†) := by
  rw [IsIsometry, ContinuousLinearMap.adjoint_adjoint]; exact ps.π_comp_adj_self i

/-- The canonical ports of `PiSum K`. -/
noncomputable def pi [DecidableEq ι] : Ports (PiSum K) K where
  π := PiSum.proj
  π_comp_adj_self i := by rw [PiSum.adjoint_proj, PiSum.proj_comp_single_same]
  π_comp_adj_ne i j h := by rw [PiSum.adjoint_proj, PiSum.proj_comp_single_of_ne h]
  sum_adj_comp := by simp only [PiSum.adjoint_proj, PiSum.sum_single_proj]

/-- The feedback operation `Q = ⊕ⱼ Oⱼ = ∑ⱼ (π j)† (O j) (π j)` (mQSP Eq. (2.2)). -/
noncomputable def feedback (O : OracleTuple K) : L →L[ℂ] L :=
  ∑ i, (ps.π i)† ∘L O i ∘L ps.π i

theorem feedback_apply (O : OracleTuple K) (v : L) :
    ps.feedback O v = ∑ i, (ps.π i)† (O i (ps.π i v)) := by
  unfold feedback
  rw [_root_.sum_apply]
  rfl

theorem π_feedback_apply (O : OracleTuple K) (j : ι) (v : L) :
    ps.π j (ps.feedback O v) = O j (ps.π j v) := by
  rw [feedback_apply, map_sum, Finset.sum_eq_single j]
  · rw [π_adj_apply_self]
  · intro i _ hij; rw [π_adj_apply_ne ps (Ne.symm hij)]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem adjoint_feedback (O : OracleTuple K) :
    (ps.feedback O)† = ps.feedback (fun i => (O i)†) := by
  simp only [feedback, map_sum, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

theorem feedback_comp_feedback (O O' : OracleTuple K) :
    ps.feedback O ∘L ps.feedback O' = ps.feedback (fun i => O i ∘L O' i) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, feedback_apply ps O,
    feedback_apply ps (fun i => O i ∘L O' i) v]
  apply Finset.sum_congr rfl
  intro i _
  rw [π_feedback_apply]; rfl

@[simp] theorem feedback_one : ps.feedback (fun i => (1 : K i →L[ℂ] K i)) = 1 := by
  ext v
  rw [feedback_apply]
  simp [ps.sum_adj_apply v]

theorem isUnitary_feedback {O : OracleTuple K} (hO : O.IsUnitary) : IsUnitary (ps.feedback O) := by
  constructor
  · rw [adjoint_feedback, feedback_comp_feedback]
    simp only [(hO _).1]
    exact ps.feedback_one
  · rw [adjoint_feedback, feedback_comp_feedback]
    simp only [(hO _).2]
    exact ps.feedback_one

theorem norm_feedback_apply {O : OracleTuple K} (hO : O.IsUnitary) (v : L) :
    ‖ps.feedback O v‖ = ‖v‖ :=
  (ps.isUnitary_feedback hO).isIsometry.norm_map v

end Ports

/-- MOD-1 (mQSP Eq. (1.1), (5.1)). A unitary junction with public space `P`, private space `L`
decomposed into ports `K j`, known unitary system matrix `S` and port delays `delay j ≥ 1`. -/
structure Junction (P : Type x) (L : Type v) [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
    (K : ι → Type w) [∀ i, HSpace (K i)] where
  /-- The system matrix `S = [[A, B], [C, D]]`, public coordinate first. -/
  S : P ⊕ₕ L →L[ℂ] P ⊕ₕ L
  /-- The system matrix is unitary. -/
  isUnitary_S : IsUnitary S
  /-- The port decomposition of the private space. -/
  ports : Ports L K
  /-- Integer port delays `rⱼ`. -/
  delay : ι → ℕ
  /-- Delays are positive. -/
  one_le_delay : ∀ i, 1 ≤ delay i

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-! ### Blocks of the system matrix -/

/-- The public-to-public block `A`. -/
noncomputable def A : P →L[ℂ] P := DSum.fst ∘L M.S ∘L DSum.inl
/-- The private-to-public block `B`. -/
noncomputable def B : L →L[ℂ] P := DSum.fst ∘L M.S ∘L DSum.inr
/-- The public-to-private block `C`. -/
noncomputable def C : P →L[ℂ] L := DSum.snd ∘L M.S ∘L DSum.inl
/-- The private-to-private block `D`. -/
noncomputable def D : L →L[ℂ] L := DSum.snd ∘L M.S ∘L DSum.inr

theorem S_eq_block : M.S = DSum.block M.A M.B M.C M.D := DSum.eq_block _

theorem S_apply (v : P ⊕ₕ L) :
    M.S v = DSum.mk (M.A (DSum.fst v) + M.B (DSum.snd v))
      (M.C (DSum.fst v) + M.D (DSum.snd v)) := by
  rw [S_eq_block, DSum.block_apply]

/-- `S† S = 1` in blocks. -/
theorem adj_mul_blocks :
    M.A† ∘L M.A + M.C† ∘L M.C = 1 ∧ M.A† ∘L M.B + M.C† ∘L M.D = 0 ∧
    M.B† ∘L M.A + M.D† ∘L M.C = 0 ∧ M.B† ∘L M.B + M.D† ∘L M.D = 1 := by
  have h := M.isUnitary_S.1
  rw [S_eq_block, DSum.adjoint_block, DSum.block_comp_block,
    ← DSum.block_one_zero_zero_one, DSum.block_ext_iff] at h
  exact h

/-- `S S† = 1` in blocks. -/
theorem mul_adj_blocks :
    M.A ∘L M.A† + M.B ∘L M.B† = 1 ∧ M.A ∘L M.C† + M.B ∘L M.D† = 0 ∧
    M.C ∘L M.A† + M.D ∘L M.B† = 0 ∧ M.C ∘L M.C† + M.D ∘L M.D† = 1 := by
  have h := M.isUnitary_S.2
  rw [S_eq_block, DSum.adjoint_block, DSum.block_comp_block,
    ← DSum.block_one_zero_zero_one, DSum.block_ext_iff] at h
  exact h

theorem opNorm_D_le_one : ‖M.D‖ ≤ 1 := by
  calc ‖M.D‖ = ‖DSum.snd ∘L M.S ∘L DSum.inr‖ := rfl
    _ ≤ ‖DSum.snd‖ * ‖M.S ∘L DSum.inr‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (1 * 1) := by
      gcongr
      · exact DSum.opNorm_snd_le
      · calc ‖M.S ∘L DSum.inr‖ ≤ ‖M.S‖ * ‖(DSum.inr : L →L[ℂ] P ⊕ₕ L)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ 1 * 1 := by
            gcongr
            · exact M.isUnitary_S.opNorm_le_one
            · exact DSum.isIsometry_inr.opNorm_le_one
    _ = 1 := by ring

/-! ### Feedback and steady state -/

/-- The feedback operation `Q = Ô(1) = ⊕ⱼ Oⱼ` of the junction's ports (mQSP Eq. (2.2)). -/
noncomputable def Q (O : OracleTuple K) : L →L[ℂ] L := M.ports.feedback O

theorem isUnitary_Q {O : OracleTuple K} (hO : O.IsUnitary) : IsUnitary (M.Q O) :=
  M.ports.isUnitary_feedback hO

/-- MOD-2. The closed loop is *regular* at `z = 1`: `1 - D Q` is invertible. -/
def IsRegular (O : OracleTuple K) : Prop := IsUnit (1 - M.D ∘L M.Q O)

/-- MOD-2 (mQSP Eq. (1.3a)). The catalyst operator `Γ = (1 - D Q)⁻¹ C`. -/
noncomputable def catalyst (O : OracleTuple K) : P →L[ℂ] L :=
  Ring.inverse (1 - M.D ∘L M.Q O) ∘L M.C

/-- MOD-2 (mQSP Eq. (1.3b)). The steady-state transfer value `F(1) = A + B Q Γ`. -/
noncomputable def steady (O : OracleTuple K) : P →L[ℂ] P :=
  M.A + M.B ∘L M.Q O ∘L M.catalyst O

/-- MOD-2 (mQSP Eq. (2.8)). The catalyst weight of port `i` on input `ψ`: `‖πᵢ Γ ψ‖²`. -/
noncomputable def weight (O : OracleTuple K) (i : ι) (ψ : P) : ℝ :=
  ‖M.ports.π i (M.catalyst O ψ)‖ ^ 2

/-- The defining fixed-point equation of the catalyst: `Γ = C + D Q Γ`. -/
theorem catalyst_eq {O : OracleTuple K} (h : M.IsRegular O) :
    M.catalyst O = M.C + M.D ∘L M.Q O ∘L M.catalyst O := by
  have h1 : (1 - M.D ∘L M.Q O) ∘L M.catalyst O = M.C := by
    rw [catalyst, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def,
      Ring.mul_inverse_cancel _ h, one_comp]
  have h2 : (1 - M.D ∘L M.Q O) ∘L M.catalyst O = M.catalyst O - M.D ∘L M.Q O ∘L M.catalyst O := by
    rw [ContinuousLinearMap.sub_comp, one_comp, ContinuousLinearMap.comp_assoc]
  rw [h2] at h1
  rw [← h1]; abel

/-- mQSP Eq. (2.7): the steady-state equation `S (ψ ⊕ Q Γ ψ) = F ψ ⊕ Γ ψ`. -/
theorem steady_state_eq {O : OracleTuple K} (h : M.IsRegular O) (ψ : P) :
    M.S (DSum.mk ψ (M.Q O (M.catalyst O ψ))) = DSum.mk (M.steady O ψ) (M.catalyst O ψ) := by
  rw [S_apply, DSum.fst_mk, DSum.snd_mk]
  have h1 : M.A ψ + M.B (M.Q O (M.catalyst O ψ)) = M.steady O ψ := rfl
  have h2 : M.C ψ + M.D (M.Q O (M.catalyst O ψ)) = M.catalyst O ψ := by
    conv_rhs => rw [catalyst_eq M h]
    rfl
  rw [h1, h2]

/-- mQSP Eq. (2.10) at `z = 1`: `‖ψ‖² + ‖Q Γ ψ‖² = ‖F ψ‖² + ‖Γ ψ‖²`. -/
theorem norm_sq_conservation {O : OracleTuple K} (h : M.IsRegular O) (ψ : P) :
    ‖ψ‖ ^ 2 + ‖M.Q O (M.catalyst O ψ)‖ ^ 2 = ‖M.steady O ψ‖ ^ 2 + ‖M.catalyst O ψ‖ ^ 2 := by
  have h1 := M.isUnitary_S.isIsometry.norm_map (DSum.mk ψ (M.Q O (M.catalyst O ψ)))
  rw [steady_state_eq M h] at h1
  have h2 := congrArg (fun t : ℝ => t ^ 2) h1
  simp only [DSum.norm_sq_eq, DSum.fst_mk, DSum.snd_mk] at h2
  exact h2.symm

/-- MOD-2 (mQSP Prop 5.1, Thm 2.1): the steady-state transfer value is unitary whenever the
oracles are unitary and the loop is regular. -/
theorem isUnitary_steady {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    IsUnitary (M.steady O) := by
  apply isUnitary_of_isIsometry
  apply isIsometry_of_norm
  intro ψ
  have h1 := M.norm_sq_conservation h ψ
  rw [(M.isUnitary_Q hO).isIsometry.norm_map] at h1
  have h2 : ‖M.steady O ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The total catalyst weight is `‖Γ ψ‖²` (sum over ports). -/
theorem sum_weight (O : OracleTuple K) (ψ : P) :
    ∑ i, M.weight O i ψ = ‖M.catalyst O ψ‖ ^ 2 :=
  (M.ports.norm_sq_eq _).symm

/-- A regular loop with `D = 0` (no private-to-private coupling) has `Γ = C` and `F = A + B Q C`. -/
theorem isRegular_of_D_eq_zero (h : M.D = 0) (O : OracleTuple K) : M.IsRegular O := by
  rw [IsRegular, h]; simp

theorem catalyst_of_D_eq_zero (h : M.D = 0) (O : OracleTuple K) : M.catalyst O = M.C := by
  rw [catalyst, h]; simp

theorem steady_of_D_eq_zero (h : M.D = 0) (O : OracleTuple K) :
    M.steady O = M.A + M.B ∘L M.Q O ∘L M.C := by
  rw [steady, catalyst_of_D_eq_zero M h]

end Junction

end MQSP
