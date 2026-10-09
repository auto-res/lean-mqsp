/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Defs

/-!
# The Cayley junction with a known load (LIB-1; mQSP Lemma 5.2, Thm 4.9)

A sum of noncommuting Hermitian signals is inserted into one Cayley transfer function.
Data: a load space `E` (public), a known Hermitian `K₀` on `E`, ports `j` with full oracle
spaces `K j` and coupling maps `Cj : E →L K j` collected in `Cc : E →L ⊕ⱼ K j`, self-inverse
unitaries `Vj` on the ports. With `R = (1 + Cc† Cc + i K₀)⁻¹` the system matrix

  `S₀ = [[2R - 1, 2 R Cc†], [2 Cc R, 2 Cc R Cc† - 1]]`,  feedback `Ô = ⊕ⱼ (-i Vj)`

is unitary, and its steady value is the Cayley transform `(1 - M)(1 + M)⁻¹` of the load
`M = i (K₀ + ∑ⱼ Cj† Vj Cj)` (mQSP Eq. (5.5)–(5.7)). The *WeightedCayley* module is the case
`K₀ = 0`, `Cj = √(λⱼ/Λ) |0⟩ⱼ`, `Vj = Be[Hⱼ/λⱼ]`, whose load is `i ∑ⱼ Hⱼ/Λ` (Eq. (5.10)).
-/

namespace MQSP

universe u v w

open scoped InnerProductSpace
open Finset

namespace Junction

variable {E : Type u} [HSpace E] {ι : Type v} [Fintype ι] [DecidableEq ι] {K : ι → Type w}
  [∀ i, HSpace (K i)]

/-- The data of a Cayley junction: known Hermitian load `K₀` and couplings `Cc`. -/
structure CayleyData (E : Type u) [HSpace E] {ι : Type v} [Fintype ι] (K : ι → Type w)
    [∀ i, HSpace (K i)] where
  /-- The known Hermitian part of the load. -/
  K₀ : E →L[ℂ] E
  /-- `K₀` is self-adjoint. -/
  K₀_adj : K₀† = K₀
  /-- The coupling map into the ports. -/
  Cc : E →L[ℂ] PiSum K

section Helpers

variable {G : Type*} [HSpace G]

/-- A skew-adjoint operator has purely imaginary expectation values. -/
theorem re_inner_eq_zero_of_adjoint_eq_neg {N : G →L[ℂ] G} (hN : N† = -N) (ψ : G) :
    RCLike.re ⟪ψ, N ψ⟫_ℂ = 0 := by
  have h1 : ⟪N ψ, ψ⟫_ℂ = -⟪ψ, N ψ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hN, neg_apply, inner_neg_right]
  have h2 := congrArg RCLike.re h1
  rw [inner_re_symm, map_neg] at h2
  linarith

/-- An operator whose real expectation values dominate `‖ψ‖²` is invertible. -/
theorem isUnit_of_le_re_inner {T : G →L[ℂ] G} (hT : ∀ ψ, ‖ψ‖ ^ 2 ≤ RCLike.re ⟪ψ, T ψ⟫_ℂ) :
    IsUnit T := by
  have hinj : Function.Injective ⇑T := by
    rw [injective_iff_map_eq_zero]
    intro ψ hψ
    have h := hT ψ
    rw [hψ, inner_zero_right, map_zero] at h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg _)))
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

theorem eq_zero_of_isUnit_apply {T : G →L[ℂ] G} (hT : IsUnit T) {y : G} (h : T y = 0) :
    y = 0 :=
  (injective_iff_map_eq_zero T).1 (ContinuousLinearMap.isUnit_iff_bijective.1 hT).1 y h

end Helpers

namespace CayleyData

variable (cd : CayleyData E K)

/-- The denominator `1 + Cc† Cc + i K₀` (with positive definite Hermitian part). -/
noncomputable abbrev denom : E →L[ℂ] E := 1 + cd.Cc† ∘L cd.Cc + Complex.I • cd.K₀

section Denom

omit [DecidableEq ι]

theorem isUnit_denom : IsUnit cd.denom := by
  apply isUnit_of_le_re_inner
  intro ψ
  have hskew : (Complex.I • cd.K₀)† = -(Complex.I • cd.K₀) := by
    rw [map_smulₛₗ, cd.K₀_adj, Complex.conj_I, neg_smul]
  have h1 := re_inner_eq_zero_of_adjoint_eq_neg hskew ψ
  rw [denom, add_apply, add_apply, one_apply_eq_self, inner_add_right, inner_add_right, map_add,
    map_add, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq, inner_self_eq_norm_sq, add_zero]
  linarith [sq_nonneg ‖cd.Cc ψ‖]

/-- `R = (1 + Cc† Cc + i K₀)⁻¹`. -/
noncomputable def R : E →L[ℂ] E := Ring.inverse cd.denom

theorem denom_comp_R : cd.denom ∘L cd.R = 1 := by
  rw [R, ← ContinuousLinearMap.mul_def, Ring.mul_inverse_cancel _ cd.isUnit_denom]

theorem R_comp_denom : cd.R ∘L cd.denom = 1 := by
  rw [R, ← ContinuousLinearMap.mul_def, Ring.inverse_mul_cancel _ cd.isUnit_denom]

theorem two_smul_eq_denom_add_adjoint :
    (2 : ℂ) • (1 + cd.Cc† ∘L cd.Cc) = cd.denom + cd.denom† := by
  simp only [denom, map_add, adjoint_one, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, map_smulₛₗ, cd.K₀_adj, Complex.conj_I]
  module

/-- mQSP Eq. (5.9): `R + R† = 2 R (1 + Cc† Cc) R†`. -/
theorem R_add_adjoint : cd.R + cd.R† = (2 : ℂ) • (cd.R ∘L (1 + cd.Cc† ∘L cd.Cc) ∘L cd.R†) := by
  have h1 : cd.R ∘L cd.denom ∘L cd.R† = cd.R† := by
    rw [← ContinuousLinearMap.comp_assoc, R_comp_denom, one_comp]
  have h2 : cd.R ∘L cd.denom† ∘L cd.R† = cd.R := by
    rw [← ContinuousLinearMap.adjoint_comp, R_comp_denom, adjoint_one, comp_one]
  rw [← ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.smul_comp,
    two_smul_eq_denom_add_adjoint, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    h1, h2, add_comm]

/-- The companion of Eq. (5.9): `R + R† = 2 R† (1 + Cc† Cc) R`. -/
theorem R_add_adjoint' :
    cd.R + cd.R† = (2 : ℂ) • (cd.R† ∘L (1 + cd.Cc† ∘L cd.Cc) ∘L cd.R) := by
  have h1 : cd.R† ∘L cd.denom ∘L cd.R = cd.R† := by
    rw [denom_comp_R, comp_one]
  have h2 : cd.R† ∘L cd.denom† ∘L cd.R = cd.R := by
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.adjoint_comp, denom_comp_R,
      adjoint_one, one_comp]
  rw [← ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.smul_comp,
    two_smul_eq_denom_add_adjoint, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    h1, h2, add_comm]

end Denom

/-- LIB-1 (mQSP Lemma 5.2, Eq. (5.7)). The Cayley junction with a known load. -/
noncomputable def junction : Junction E (PiSum K) K where
  S := DSum.block ((2 : ℂ) • cd.R - 1) ((2 : ℂ) • (cd.R ∘L cd.Cc†)) ((2 : ℂ) • (cd.Cc ∘L cd.R))
    ((2 : ℂ) • (cd.Cc ∘L cd.R ∘L cd.Cc†) - 1)
  isUnitary_S := by
    have hZ : (2 : ℂ) • (cd.R† ∘L cd.R + cd.R† ∘L cd.Cc† ∘L cd.Cc ∘L cd.R) - cd.R - cd.R† = 0 := by
      rw [sub_sub, sub_eq_zero, cd.R_add_adjoint']
      simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, one_comp,
        ContinuousLinearMap.comp_assoc]
    have hW : (2 : ℂ) • (cd.R ∘L cd.R† + cd.R ∘L cd.Cc† ∘L cd.Cc ∘L cd.R†) - cd.R - cd.R† = 0 := by
      rw [sub_sub, sub_eq_zero, cd.R_add_adjoint]
      simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, one_comp,
        ContinuousLinearMap.comp_assoc]
    refine ⟨?_, ?_⟩ <;>
      rw [DSum.adjoint_block, DSum.block_comp_block, ← DSum.block_one_zero_zero_one,
        DSum.block_ext_iff] <;>
      simp only [map_sub, map_smulₛₗ, adjoint_one, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, map_ofNat] <;>
      refine ⟨?_, ?_, ?_, ?_⟩
    on_goal 1 => linear_combination (norm := skip) (2 : ℂ) • hZ
    on_goal 2 => linear_combination (norm := skip) (2 : ℂ) • congrArg (· ∘L cd.Cc†) hZ
    on_goal 3 => linear_combination (norm := skip) (2 : ℂ) • congrArg (cd.Cc ∘L ·) hZ
    on_goal 4 =>
      linear_combination (norm := skip) (2 : ℂ) • congrArg (fun T => cd.Cc ∘L T ∘L cd.Cc†) hZ
    on_goal 5 => linear_combination (norm := skip) (2 : ℂ) • hW
    on_goal 6 => linear_combination (norm := skip) (2 : ℂ) • congrArg (· ∘L cd.Cc†) hW
    on_goal 7 => linear_combination (norm := skip) (2 : ℂ) • congrArg (cd.Cc ∘L ·) hW
    on_goal 8 =>
      linear_combination (norm := skip) (2 : ℂ) • congrArg (fun T => cd.Cc ∘L T ∘L cd.Cc†) hW
    all_goals
      simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, one_comp, comp_one,
        ContinuousLinearMap.comp_assoc, smul_smul, ContinuousLinearMap.comp_zero,
        ContinuousLinearMap.zero_comp]
      module
  ports := Ports.pi
  delay _ := 1
  one_le_delay _ := le_rfl

@[simp] theorem junction_A : cd.junction.A = (2 : ℂ) • cd.R - 1 := DSum.fst_block_inl _ _ _ _
@[simp] theorem junction_B : cd.junction.B = (2 : ℂ) • (cd.R ∘L cd.Cc†) :=
  DSum.fst_block_inr _ _ _ _
@[simp] theorem junction_C : cd.junction.C = (2 : ℂ) • (cd.Cc ∘L cd.R) :=
  DSum.snd_block_inl _ _ _ _
@[simp] theorem junction_D : cd.junction.D = (2 : ℂ) • (cd.Cc ∘L cd.R ∘L cd.Cc†) - 1 :=
  DSum.snd_block_inr _ _ _ _

/-- The feedback of the Cayley junction is the port-diagonal operator `⊕ⱼ Oⱼ`. -/
theorem junction_Q (O : OracleTuple K) : cd.junction.Q O = PiSum.diag O := by
  change (∑ i, (PiSum.proj i)† ∘L O i ∘L PiSum.proj i) = _
  simp only [PiSum.adjoint_proj]
  rfl

/-- The feedback operators `-i Vⱼ` of the Cayley junction (phase convention of Eq. (5.7)). -/
noncomputable def oracles (V : OracleTuple K) : OracleTuple K := fun j => (-Complex.I) • V j

/-- The load `M = i (K₀ + ∑ⱼ Cj† Vj Cj) = i (K₀ + Cc† (⊕ⱼ Vj) Cc)` at `z = 1` (Eq. (5.6)). -/
noncomputable def load (V : OracleTuple K) : E →L[ℂ] E :=
  Complex.I • (cd.K₀ + cd.Cc† ∘L PiSum.diag V ∘L cd.Cc)

/-- Self-inverse oracles: `Vⱼ† = Vⱼ` and `Vⱼ Vⱼ = 1`. -/
def SelfInverse (V : OracleTuple K) : Prop := ∀ j, (V j)† = V j ∧ V j ∘L V j = 1

/-- The load has Hermitian part `0` at `z = 1` (it is `i` times a self-adjoint operator). -/
theorem load_adjoint {V : OracleTuple K} (hV : SelfInverse V) : (cd.load V)† = -cd.load V := by
  have hVadj : (PiSum.diag V)† = PiSum.diag V := by
    rw [PiSum.adjoint_diag]
    simp only [(hV _).1]
  simp only [load, map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hVadj, cd.K₀_adj, Complex.conj_I, neg_smul,
    ContinuousLinearMap.comp_assoc]

theorem isUnit_one_add_load {V : OracleTuple K} (hV : SelfInverse V) : IsUnit (1 + cd.load V) := by
  apply isUnit_of_le_re_inner
  intro ψ
  rw [add_apply, one_apply_eq_self, inner_add_right, map_add,
    re_inner_eq_zero_of_adjoint_eq_neg (cd.load_adjoint hV) ψ, add_zero, inner_self_eq_norm_sq]

theorem diag_diag_apply {V : OracleTuple K} (hV : SelfInverse V) (y : PiSum K) :
    PiSum.diag V (PiSum.diag V y) = y := by
  rw [← ContinuousLinearMap.comp_apply, PiSum.diag_comp_diag]
  simp only [(hV _).2, PiSum.diag_one, one_apply_eq_self]

theorem junction_Q_oracles (V : OracleTuple K) :
    cd.junction.Q (oracles V) = (-Complex.I) • PiSum.diag V := by
  rw [junction_Q, PiSum.diag, PiSum.diag, Finset.smul_sum]
  simp only [oracles, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

/-- The wave-digital elimination of the Cayley junction (mQSP Eq. (4.97)): if `γ` solves the
private fixed-point equation `γ = C ψ + D Q γ`, then `h = R (ψ + Cc† Q γ)` solves
`(1 + M) h = ψ` and `γ = Cc h - Q Cc h`. -/
theorem elim {V : OracleTuple K} (hV : SelfInverse V) (ψ : E) (γ : PiSum K)
    (hγ : γ = cd.junction.C ψ + cd.junction.D (cd.junction.Q (oracles V) γ)) :
    (1 + cd.load V) (cd.R (ψ + cd.Cc† (cd.junction.Q (oracles V) γ))) = ψ ∧
      γ = cd.Cc (cd.R (ψ + cd.Cc† (cd.junction.Q (oracles V) γ))) -
        cd.junction.Q (oracles V) (cd.Cc (cd.R (ψ + cd.Cc† (cd.junction.Q (oracles V) γ)))) := by
  have hQ := cd.junction_Q_oracles V
  have hQQ : ∀ y, cd.junction.Q (oracles V) (cd.junction.Q (oracles V) y) = -y := by
    intro y
    rw [hQ]
    simp only [smul_apply, map_smul, diag_diag_apply hV, smul_smul, neg_mul_neg,
      Complex.I_mul_I, neg_one_smul]
  have hIV : ∀ y, Complex.I • cd.Cc† (PiSum.diag V y) = -cd.Cc† (cd.junction.Q (oracles V) y) := by
    intro y
    rw [hQ, smul_apply, map_smul, neg_smul, neg_neg]
  rw [junction_C, junction_D] at hγ
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self] at hγ
  generalize cd.junction.Q (oracles V) = Q at hQQ hIV hγ ⊢
  generalize hh : cd.R (ψ + cd.Cc† (Q γ)) = h
  have hden : h + cd.Cc† (cd.Cc h) + Complex.I • cd.K₀ h = ψ + cd.Cc† (Q γ) := by
    rw [← hh]
    have := congrArg (· (ψ + cd.Cc† (Q γ))) cd.denom_comp_R
    simpa using this
  have f2 : γ = (2 : ℂ) • cd.Cc h - Q γ := by
    rw [← hh, map_add, map_add]
    linear_combination (norm := module) hγ
  have f3 : Q γ = (2 : ℂ) • Q (cd.Cc h) + γ := by
    have := congrArg Q f2
    rw [map_sub, map_smul, hQQ] at this
    rw [this, sub_neg_eq_add]
  have f4 : Q γ = cd.Cc h + Q (cd.Cc h) := by
    linear_combination (norm := module) (1 / 2 : ℂ) • f3 + (1 / 2 : ℂ) • f2
  refine ⟨?_, ?_⟩
  · have hC4 : cd.Cc† (Q γ) = cd.Cc† (cd.Cc h) + cd.Cc† (Q (cd.Cc h)) := by
      rw [f4, map_add]
    simp only [load, add_apply, one_apply_eq_self, smul_apply, ContinuousLinearMap.comp_apply,
      smul_add, hIV]
    linear_combination (norm := module) hden + hC4
  · linear_combination (norm := module) f2 - f4

/-- The Cayley junction is regular for self-inverse oracles. -/
theorem isRegular {V : OracleTuple K} (hV : SelfInverse V) :
    cd.junction.IsRegular (oracles V) := by
  rw [isRegular_iff_injective, injective_iff_map_eq_zero]
  intro v hv
  rw [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, sub_eq_zero] at hv
  have hγ : v = cd.junction.C 0 + cd.junction.D (cd.junction.Q (oracles V) v) := by
    rw [map_zero, zero_add]
    exact hv
  obtain ⟨h1, h2⟩ := cd.elim hV 0 v hγ
  rw [eq_zero_of_isUnit_apply (cd.isUnit_one_add_load hV) h1, map_zero, map_zero, sub_zero] at h2
  exact h2

/-- LIB-1 (mQSP Lemma 5.2, Eq. (5.5b)/(5.6)). The steady value of the Cayley junction is the
Cayley transform `(1 - M)(1 + M)⁻¹` of the load. -/
theorem steady_eq {V : OracleTuple K} (hV : SelfInverse V) :
    cd.junction.steady (oracles V) =
      (1 - cd.load V) ∘L Ring.inverse (1 + cd.load V) := by
  have hreg := cd.isRegular hV
  have hU := cd.isUnit_one_add_load hV
  ext ψ
  have hfix : cd.junction.catalyst (oracles V) ψ = cd.junction.C ψ +
      cd.junction.D (cd.junction.Q (oracles V) (cd.junction.catalyst (oracles V) ψ)) := by
    conv_lhs => rw [cd.junction.catalyst_eq hreg]
    rfl
  obtain ⟨h1, -⟩ := cd.elim hV ψ _ hfix
  have hst : cd.junction.steady (oracles V) ψ = cd.junction.A ψ +
      cd.junction.B (cd.junction.Q (oracles V) (cd.junction.catalyst (oracles V) ψ)) := rfl
  rw [hst, ContinuousLinearMap.comp_apply]
  generalize cd.junction.Q (oracles V) (cd.junction.catalyst (oracles V) ψ) = q at h1 ⊢
  generalize hh : cd.R (ψ + cd.Cc† q) = h at h1
  have hinv : Ring.inverse (1 + cd.load V) ψ = h := by
    calc Ring.inverse (1 + cd.load V) ψ = Ring.inverse (1 + cd.load V) ((1 + cd.load V) h) := by
          rw [h1]
      _ = (Ring.inverse (1 + cd.load V) * (1 + cd.load V)) h := rfl
      _ = h := by rw [Ring.inverse_mul_cancel _ hU, one_apply_eq_self]
  have hh' : cd.R ψ + cd.R (cd.Cc† q) = h := by rw [← hh, map_add]
  rw [hinv, junction_A, junction_B]
  simp only [sub_apply, add_apply, smul_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply] at h1 ⊢
  linear_combination (norm := module) (2 : ℂ) • hh' + h1

end CayleyData

end Junction

end MQSP
