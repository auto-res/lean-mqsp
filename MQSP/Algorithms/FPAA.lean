/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Modules.Query
import MQSP.Modules.Cayley
import MQSP.Compile.Lift

/-!
# Fixed-point amplitude amplification by feedback (ALG-FPAA; mQSP §1.1.1, §5.3.1)

The FPAA tap is the two-dimensional (good/bad) model of mQSP Eq. (1.38): public space `ℂ`,
private space `Reg 2 ℂ` (slot `0` = good, slot `1` = bad), system matrix

  `S = [[c, -√(1-c²), 0], [√(1-c²), c, 0], [0, 0, 1]]`  (`0 < c < 1`),

and feedback through the Grover rotation `O_θ = [[cos 2θ, sin 2θ], [-sin 2θ, cos 2θ]]`.
At `z = 1` the steady-state equations give (for `sin θ ≠ 0`)

* catalyst `Γ u = √((1-c)/(1+c)) · (u, -cot θ · u)` (Eq. (1.39)),
  weight `‖Γ‖² = (1-c)/((1+c) sin² θ)`;
* transfer value `F = 1` (the all-pass BiQuad `FPAA(λ) = 1`, Eq. (1.35)).

For state preparation one feeds the prepared state `(sin θ, cos θ)` into the private register
with zero public input; each round transmits part of the good amplitude to a fresh public
slot and the private residual after `N` rounds is `K^N (sin θ, cos θ)` with
`K = diag(c, 1) ∘ O_θ` (Eq. (1.41)). The residual decays geometrically (Eq. (1.42a)):
`‖K^N‖ ≤ c^{N/2} (1 + N (1-c)/√c)` (Schur-form estimate, optional here).
-/

namespace MQSP

universe u

namespace Junction

/-- The Grover rotation by `2θ` on the good/bad plane `Reg 2 ℂ`. -/
noncomputable def grover (θ : ℝ) : Reg 2 ℂ →L[ℂ] Reg 2 ℂ :=
  Reg.single 0 ∘L ((Real.cos (2 * θ) : ℂ) • 1) ∘L Reg.proj 0 +
  Reg.single 0 ∘L ((Real.sin (2 * θ) : ℂ) • 1) ∘L Reg.proj 1 +
  Reg.single 1 ∘L ((-Real.sin (2 * θ) : ℂ) • 1) ∘L Reg.proj 0 +
  Reg.single 1 ∘L ((Real.cos (2 * θ) : ℂ) • 1) ∘L Reg.proj 1

section Helpers

theorem fpaa_fin_zero_ne_one : (0 : Fin 2) ≠ 1 := by decide

theorem fpaa_fin_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

theorem fpaa_reg2_ext {v w : Reg 2 ℂ} (h0 : Reg.proj 0 v = Reg.proj 0 w)
    (h1 : Reg.proj 1 v = Reg.proj 1 w) : v = w := by
  rw [← reg2_decomp v, ← reg2_decomp w, h0, h1]

theorem grover_proj0 (θ : ℝ) (v : Reg 2 ℂ) :
    Reg.proj 0 (grover θ v) =
      (Real.cos (2 * θ) : ℂ) * Reg.proj 0 v + (Real.sin (2 * θ) : ℂ) * Reg.proj 1 v := by
  simp [grover, Reg.proj_single_of_ne fpaa_fin_zero_ne_one]

theorem grover_proj1 (θ : ℝ) (v : Reg 2 ℂ) :
    Reg.proj 1 (grover θ v) =
      -(Real.sin (2 * θ) : ℂ) * Reg.proj 0 v + (Real.cos (2 * θ) : ℂ) * Reg.proj 1 v := by
  simp [grover, Reg.proj_single_of_ne fpaa_fin_one_ne_zero]

theorem fpaa_cos_two_mul (θ : ℝ) :
    (Real.cos (2 * θ) : ℂ) = 2 * (Real.cos θ : ℂ) ^ 2 - 1 := by
  rw [Real.cos_two_mul]; push_cast; ring

theorem fpaa_sin_two_mul (θ : ℝ) :
    (Real.sin (2 * θ) : ℂ) = 2 * (Real.sin θ : ℂ) * Real.cos θ := by
  rw [Real.sin_two_mul]; push_cast; ring

theorem fpaa_sin_sq_add_cos_sq (θ : ℝ) :
    (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq θ

/-- `√(1 - c²) = √((1-c)/(1+c)) (1 + c)` for `0 < c < 1`. -/
theorem fpaa_sqrt_eq {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Real.sqrt (1 - c ^ 2) = Real.sqrt ((1 - c) / (1 + c)) * (1 + c) := by
  have h1 : 1 - c ^ 2 = (1 - c) / (1 + c) * (1 + c) ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sqrt_mul (div_nonneg (by linarith) (by linarith)), Real.sqrt_sq (by linarith)]

end Helpers

theorem isUnitary_grover (θ : ℝ) : IsUnitary (grover θ) := by
  refine isUnitary_of_isIsometry (isIsometry_of_norm fun v => ?_)
  have h := Real.cos_sq_add_sin_sq (2 * θ)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Reg.norm_sq_eq, Reg.norm_sq_eq v,
    Fin.sum_univ_two, Fin.sum_univ_two, grover_proj0, grover_proj1]
  generalize Reg.proj 0 v = g
  generalize Reg.proj 1 v = b
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  linear_combination (g.re ^ 2 + g.im ^ 2 + b.re ^ 2 + b.im ^ 2) * h

/-- The FPAA system matrix (Eq. (1.38)) is unitary: a rotation by `arccos c` on the
public/good plane, the identity on the bad slot. -/
theorem fpaa_isUnitary_S {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IsUnitary (DSum.block ((c : ℂ) • (1 : ℂ →L[ℂ] ℂ))
      ((-(Real.sqrt (1 - c ^ 2)) : ℂ) • (Reg.proj 0 : Reg 2 ℂ →L[ℂ] ℂ))
      ((Real.sqrt (1 - c ^ 2) : ℂ) • (Reg.single 0 : ℂ →L[ℂ] Reg 2 ℂ))
      (Reg.single 0 ∘L ((c : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ∘L Reg.proj 0 +
        Reg.single 1 ∘L Reg.proj 1)) := by
  refine isUnitary_of_isIsometry (isIsometry_of_norm fun v => ?_)
  have h : c ^ 2 + Real.sqrt (1 - c ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by nlinarith)]; ring
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), DSum.norm_sq_eq, DSum.norm_sq_eq v,
    Reg.norm_sq_eq, Reg.norm_sq_eq (DSum.snd v), Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Complex.coe_smul, Fin.isValue, neg_smul, ContinuousLinearMap.smul_comp, one_comp,
    ContinuousLinearMap.comp_smul, DSum.fst_block_apply, smul_apply, one_apply_eq_self,
    Complex.real_smul, neg_apply, DSum.snd_block_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_add, ContinuousLinearMap.map_smul_of_tower,
    PiSum.proj_single_same, ne_eq, zero_ne_one, not_false_eq_true, PiSum.proj_single_of_ne,
    add_zero, one_ne_zero, smul_zero, zero_add]
  generalize DSum.fst v = u
  generalize Reg.proj 0 (DSum.snd v) = g
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  linear_combination (u.re ^ 2 + u.im ^ 2 + g.re ^ 2 + g.im ^ 2) * h

/-- ALG-FPAA (mQSP Eq. (1.38)). The FPAA tap junction with damping `c`. -/
noncomputable def fpaa (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    Junction ℂ (Reg 2 ℂ) (onePort (Reg 2 ℂ)) where
  S := DSum.block ((c : ℂ) • 1) ((-(Real.sqrt (1 - c ^ 2)) : ℂ) • Reg.proj 0)
    ((Real.sqrt (1 - c ^ 2) : ℂ) • Reg.single 0)
    (Reg.single 0 ∘L ((c : ℂ) • 1) ∘L Reg.proj 0 + Reg.single 1 ∘L Reg.proj 1)
  isUnitary_S := fpaa_isUnitary_S hc hc1
  ports := Ports.one (Reg 2 ℂ)
  delay _ := 1
  one_le_delay _ := le_rfl

variable {c : ℝ} (hc : 0 < c) (hc1 : c < 1) {θ : ℝ} (hθ : Real.sin θ ≠ 0)

@[simp] theorem fpaa_A : (fpaa c hc hc1).A = (c : ℂ) • 1 := DSum.fst_block_inl _ _ _ _
@[simp] theorem fpaa_B :
    (fpaa c hc hc1).B = (-(Real.sqrt (1 - c ^ 2)) : ℂ) • Reg.proj 0 :=
  DSum.fst_block_inr _ _ _ _
@[simp] theorem fpaa_C : (fpaa c hc hc1).C = (Real.sqrt (1 - c ^ 2) : ℂ) • Reg.single 0 :=
  DSum.snd_block_inl _ _ _ _
@[simp] theorem fpaa_D :
    (fpaa c hc hc1).D = Reg.single 0 ∘L ((c : ℂ) • 1) ∘L Reg.proj 0 + Reg.single 1 ∘L Reg.proj 1 :=
  DSum.snd_block_inr _ _ _ _
@[simp] theorem fpaa_π (i : One) : (fpaa c hc hc1).ports.π i = 1 := rfl

theorem fpaa_Q (U : Reg 2 ℂ →L[ℂ] Reg 2 ℂ) : (fpaa c hc hc1).Q (oneOracle U) = U := by
  rw [Q, Ports.feedback, Fintype.sum_unique]
  simp only [fpaa_π, adjoint_one, one_comp, comp_one]
  rfl

theorem fpaa_D_proj0 (w : Reg 2 ℂ) : Reg.proj 0 ((fpaa c hc hc1).D w) = (c : ℂ) * Reg.proj 0 w := by
  simp [Reg.proj_single_of_ne fpaa_fin_zero_ne_one]

theorem fpaa_D_proj1 (w : Reg 2 ℂ) : Reg.proj 1 ((fpaa c hc hc1).D w) = Reg.proj 1 w := by
  simp [Reg.proj_single_of_ne fpaa_fin_one_ne_zero]

include hθ in
/-- The loop is regular when `sin θ ≠ 0`. -/
theorem fpaa_isRegular : (fpaa c hc hc1).IsRegular (oneOracle (grover θ)) := by
  rw [isRegular_iff_injective, injective_iff_map_eq_zero, fpaa_Q]
  intro v hv
  have e0 := congrArg (Reg.proj 0) hv
  have e1 := congrArg (Reg.proj 1) hv
  simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub,
    fpaa_D_proj0, fpaa_D_proj1, grover_proj0, grover_proj1, map_zero,
    fpaa_cos_two_mul, fpaa_sin_two_mul] at e0 e1
  have hsc := fpaa_sin_sq_add_cos_sq θ
  have hs0 : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ
  have hc0 : (1 + (c : ℂ)) ≠ 0 := by
    have : (1 + c : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have e3 : (Real.sin θ : ℂ) * Reg.proj 1 v + Real.cos θ * Reg.proj 0 v = 0 := by
    have : (2 * (Real.sin θ : ℂ)) *
        ((Real.sin θ : ℂ) * Reg.proj 1 v + Real.cos θ * Reg.proj 0 v) = 0 := by
      linear_combination e1 + 2 * Reg.proj 1 v * hsc
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero hs0)
  have hg : Reg.proj 0 v = 0 := by
    have : ((1 + (c : ℂ)) * Real.sin θ) * Reg.proj 0 v = 0 := by
      linear_combination (Real.sin θ : ℂ) * e0 + 2 * c * Real.sin θ * Real.cos θ * e3
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hc0 hs0)
  have hb : Reg.proj 1 v = 0 := by
    rw [hg, mul_zero, add_zero] at e3
    exact (mul_eq_zero.1 e3).resolve_left hs0
  exact fpaa_reg2_ext (by rw [hg, map_zero]) (by rw [hb, map_zero])

include hθ in
/-- ALG-FPAA (mQSP Eq. (1.39)). The catalyst: `Γ u = √((1-c)/(1+c)) (u, -cot θ u)`. -/
theorem fpaa_catalyst (u : ℂ) :
    (fpaa c hc hc1).catalyst (oneOracle (grover θ)) u =
      (Real.sqrt ((1 - c) / (1 + c)) : ℂ) •
        (Reg.single 0 u + Reg.single 1 ((-(Real.cos θ / Real.sin θ) : ℂ) • u)) := by
  set Γ : ℂ →L[ℂ] Reg 2 ℂ := (Real.sqrt ((1 - c) / (1 + c)) : ℂ) •
    (Reg.single 0 + Reg.single 1 ∘L ((-(Real.cos θ / Real.sin θ) : ℂ) • 1)) with hΓdef
  have hΓu : ∀ u, Γ u = (Real.sqrt ((1 - c) / (1 + c)) : ℂ) •
        (Reg.single 0 u + Reg.single 1 ((-(Real.cos θ / Real.sin θ) : ℂ) • u)) := by
    intro u
    simp only [Γ, smul_apply, add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self]
  have hΓ0 : ∀ w, Reg.proj 0 (Γ w) = (Real.sqrt ((1 - c) / (1 + c)) : ℂ) * w := by
    intro w
    rw [hΓu]
    simp only [map_smul, map_add, Reg.proj_single_same, Reg.proj_single_of_ne fpaa_fin_zero_ne_one,
      smul_eq_mul, add_zero]
  have hΓ1 : ∀ w, Reg.proj 1 (Γ w) =
      (Real.sqrt ((1 - c) / (1 + c)) : ℂ) * ((-(Real.cos θ / Real.sin θ) : ℂ) * w) := by
    intro w
    rw [hΓu]
    simp only [map_smul, map_add, Reg.proj_single_same, Reg.proj_single_of_ne fpaa_fin_one_ne_zero,
      smul_eq_mul, zero_add]
  have hs0 : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ
  have hσ : (Real.sqrt (1 - c ^ 2) : ℂ) = (Real.sqrt ((1 - c) / (1 + c)) : ℂ) * (1 + c) := by
    rw [fpaa_sqrt_eq hc hc1]; push_cast; ring
  have hsc := fpaa_sin_sq_add_cos_sq θ
  rw [← hΓu]
  refine congrArg (fun T : ℂ →L[ℂ] Reg 2 ℂ => T u)
    ((fpaa c hc hc1).catalyst_unique (fpaa_isRegular hc hc1 hθ) ?_).symm
  refine ContinuousLinearMap.ext fun w => fpaa_reg2_ext ?_ ?_
  · simp only [add_apply, ContinuousLinearMap.comp_apply, fpaa_C, fpaa_Q, smul_apply, map_add,
      map_smul, fpaa_D_proj0, grover_proj0, hΓ0, hΓ1, Reg.proj_single_same, smul_eq_mul,
      fpaa_cos_two_mul, fpaa_sin_two_mul, hσ]
    field_simp
    ring
  · simp only [add_apply, ContinuousLinearMap.comp_apply, fpaa_C, fpaa_Q, smul_apply, map_add,
      map_smul, fpaa_D_proj1, grover_proj1, hΓ0, hΓ1, Reg.proj_single_of_ne fpaa_fin_one_ne_zero,
      smul_zero, zero_add, fpaa_cos_two_mul, fpaa_sin_two_mul]
    field_simp
    linear_combination (2 * (Real.sqrt ((1 - c) / (1 + c)) : ℂ) * Real.cos θ * w) * hsc

include hθ in
/-- ALG-FPAA. The catalyst weight is `(1-c)/((1+c) sin² θ)` per unit input. -/
theorem fpaa_weight (u : ℂ) :
    (fpaa c hc hc1).weight (oneOracle (grover θ)) () u =
      (1 - c) / ((1 + c) * Real.sin θ ^ 2) * ‖u‖ ^ 2 := by
  rw [weight, fpaa_π, one_apply_eq_self, fpaa_catalyst hc hc1 hθ, norm_smul, mul_pow,
    reg2_norm_sq_single_add, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (div_nonneg (by linarith) (by linarith)), norm_neg, norm_div,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, div_pow, sq_abs,
    sq_abs]
  have h := Real.sin_sq_add_cos_sq θ
  have hs2 : Real.sin θ ^ 2 ≠ 0 := pow_ne_zero 2 hθ
  have hc0 : 1 + c ≠ 0 := by linarith
  field_simp
  linear_combination (1 - c) * ‖u‖ ^ 2 * h

include hθ in
/-- ALG-FPAA (mQSP Eq. (1.35): `FPAA(λ) = 1`). The steady value of the tap is the identity. -/
theorem fpaa_steady : (fpaa c hc hc1).steady (oneOracle (grover θ)) = 1 := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [steady, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    fpaa_catalyst hc hc1 hθ, fpaa_A, fpaa_B, fpaa_Q]
  simp only [smul_apply, one_apply_eq_self, grover_proj0, map_smul, map_add,
    Reg.proj_single_same, Reg.proj_single_of_ne fpaa_fin_zero_ne_one,
    Reg.proj_single_of_ne fpaa_fin_one_ne_zero, smul_eq_mul, mul_zero, add_zero,
    fpaa_cos_two_mul, fpaa_sin_two_mul]
  have hs0 : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hθ
  have hσ : (Real.sqrt (1 - c ^ 2) : ℂ) = (Real.sqrt ((1 - c) / (1 + c)) : ℂ) * (1 + c) := by
    rw [fpaa_sqrt_eq hc hc1]; push_cast; ring
  have hσ2 : (Real.sqrt ((1 - c) / (1 + c)) : ℂ) ^ 2 * (1 + c) = 1 - c := by
    have h1 : Real.sqrt ((1 - c) / (1 + c)) ^ 2 * (1 + c) = 1 - c := by
      rw [Real.sq_sqrt (div_nonneg (by linarith) (by linarith))]
      field_simp
    exact_mod_cast h1
  rw [hσ]
  field_simp
  linear_combination u * hσ2

/-- The private update per round, `K = D ∘ O_θ = diag(c, 1) ∘ grover θ` (Eq. (1.41)). -/
noncomputable def fpaaK (c θ : ℝ) : Reg 2 ℂ →L[ℂ] Reg 2 ℂ :=
  (Reg.single 0 ∘L ((c : ℂ) • 1) ∘L Reg.proj 0 + Reg.single 1 ∘L Reg.proj 1) ∘L grover θ

theorem fpaa_D_comp_Q :
    (fpaa c hc hc1).D ∘L (fpaa c hc hc1).Q (oneOracle (grover θ)) = fpaaK c θ := by
  rw [fpaa_D, fpaa_Q]
  rfl

/-! The decay bound of Eq. (1.42a), `‖K^N‖ ≤ c^{N/2} (1 + N (1 - c)/√c)`, holds in the
under-damped regime `(1 + c)² cos²(2θ) ≤ 4c` (both eigenvalues of `K` then have modulus `√c`;
Schur-form estimate with off-diagonal entry of modulus `1 - c`). It fails outside that regime
(e.g. `c = 1/4`, `θ = π/2` gives `K = -diag(1/4, 1)`, `‖K³‖ = 1`). Its formalisation is future
work (see `dev/formal-spec.md`, LIB-3). -/

end Junction

end MQSP
