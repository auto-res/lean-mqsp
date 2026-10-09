/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg
import MQSP.Modules.Query

/-!
# The Cayley module (LIB-1; mQSP §1.1 Eq. (1.21)–(1.31), §5.3.4 Eq. (5.35))

For a self-inverse block encoding `O = Be[H/λ]` with signal projector `Π = |0⟩⟨0|ₐ ⊗ I` on the
oracle space `K = Reg 2 E` (ancilla qubit `a` ⊗ system `E`), the Cayley module has public
space `E`, private space `K`, one port carrying `O`, and the system matrix (Eq. (5.35))

  `S = [[0, -i ⟨0|ₐ], [|0⟩ₐ, i (1 - Π)]]`.

Its transfer function is `z (z - i x)/(1 + i x z)` on an eigenvector with `⟨0|ₐ O |0⟩ₐ = x`;
at `z = 1` the steady value is the Cayley transform `(1 - i A)(1 + i A)⁻¹ = e^{-2i arctan A}`
of the encoded Hermitian contraction `A = ⟨0|ₐ O |0⟩ₐ`, and the catalyst weight on a unit
eigenvector with eigenvalue `x` is `2/(1 + x²)` (Eq. (1.27)).
-/

namespace MQSP

universe u

open scoped InnerProductSpace

namespace Junction

variable (E : Type u) [HSpace E]

/-- The signal injection `|0⟩ₐ ⊗ I : E → Reg 2 E`. -/
noncomputable abbrev sig : E →L[ℂ] Reg 2 E := Reg.single 0

/-- The signal projector `Π = |0⟩⟨0|ₐ ⊗ I` on `Reg 2 E`. -/
noncomputable abbrev sigProj : Reg 2 E →L[ℂ] Reg 2 E := Reg.single 0 ∘L Reg.proj 0

section Helpers

variable {E}

theorem reg2_single_proj_add :
    (Reg.single 0 ∘L Reg.proj 0 + Reg.single 1 ∘L Reg.proj 1 : Reg 2 E →L[ℂ] Reg 2 E) = 1 := by
  rw [← Reg.sum_single_proj, Fin.sum_univ_two]

theorem one_sub_sigProj : 1 - sigProj E = Reg.single 1 ∘L Reg.proj 1 := by
  rw [← reg2_single_proj_add]; abel

theorem reg2_proj_comp_single_same (a : Fin 2) :
    (Reg.proj a ∘L Reg.single a : E →L[ℂ] E) = 1 :=
  PiSum.proj_comp_single_same a

theorem reg2_proj0_comp_single1 : (Reg.proj (n := 2) 0 ∘L Reg.single 1 : E →L[ℂ] E) = 0 :=
  PiSum.proj_comp_single_of_ne (by decide)

theorem reg2_proj1_comp_single0 : (Reg.proj (n := 2) 1 ∘L Reg.single 0 : E →L[ℂ] E) = 0 :=
  PiSum.proj_comp_single_of_ne (by decide)

variable {G : Type*} [HSpace G]

open scoped InnerProductSpace

theorem reg2_proj_single_comp_same (a : Fin 2) (f : G →L[ℂ] E) :
    Reg.proj a ∘L (Reg.single a ∘L f) = f := by
  rw [← ContinuousLinearMap.comp_assoc, reg2_proj_comp_single_same, one_comp]

theorem reg2_proj0_single1_comp (f : G →L[ℂ] E) :
    Reg.proj (n := 2) 0 ∘L (Reg.single 1 ∘L f) = 0 := by
  rw [← ContinuousLinearMap.comp_assoc, reg2_proj0_comp_single1, ContinuousLinearMap.zero_comp]

theorem reg2_proj1_single0_comp (f : G →L[ℂ] E) :
    Reg.proj (n := 2) 1 ∘L (Reg.single 0 ∘L f) = 0 := by
  rw [← ContinuousLinearMap.comp_assoc, reg2_proj1_comp_single0, ContinuousLinearMap.zero_comp]

theorem reg2_decomp (v : Reg 2 E) :
    Reg.single 0 (Reg.proj 0 v) + Reg.single 1 (Reg.proj 1 v) = v := by
  have := congrArg (fun T : Reg 2 E →L[ℂ] Reg 2 E => T v) reg2_single_proj_add
  simpa using this

theorem reg2_norm_sq_single_add (a b : E) :
    ‖(Reg.single 0 a + Reg.single 1 b : Reg 2 E)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [Reg.norm_sq_eq, Fin.sum_univ_two]
  simp

theorem conj_I_ne : (starRingEnd ℂ) Complex.I ≠ Complex.I := by
  rw [Complex.conj_I]
  intro h
  have := congrArg Complex.im h
  norm_num at this

theorem conj_neg_I_ne : (starRingEnd ℂ) (-Complex.I) ≠ -Complex.I := by
  rw [map_neg]
  exact fun h => conj_I_ne (neg_inj.1 h)

/-- A self-adjoint operator has no eigenvalue `z` with `z̄ ≠ z`. -/
theorem eq_zero_of_apply_eq_smul {T : G →L[ℂ] G} (hT : T† = T) {z : ℂ}
    (hz : (starRingEnd ℂ) z ≠ z) {v : G} (h : T v = z • v) : v = 0 := by
  have h1 : ⟪T v, v⟫_ℂ = ⟪v, T v⟫_ℂ := by
    conv_rhs => rw [← hT]
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [h, inner_smul_left, inner_smul_right] at h1
  have h2 : ⟪v, v⟫_ℂ = 0 := by
    by_contra hne
    exact hz (mul_right_cancel₀ hne h1)
  exact inner_self_eq_zero.1 h2

/-- The algebraic core of the Cayley steady value: if `[[a, b], [c, d]]` squares to the identity
in its first column/row and `g = i (c + d g)`, then `(1 + i a)(-i (a + b g)) = 1 - i a`. -/
theorem cayley_alg {R : Type*} [Ring R] [Algebra ℂ R] {a b c d g : R}
    (h00 : a * a + b * c = 1) (h01 : a * b + b * d = 0) (hg : g = Complex.I • (c + d * g)) :
    (1 + Complex.I • a) * ((-Complex.I) • (a + b * g)) = 1 - Complex.I • a := by
  have hIg : Complex.I • g = -(c + d * g) := by
    conv_lhs => rw [hg]
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hab : a * b = -(b * d) := eq_neg_of_add_eq_zero_left h01
  have hdg : d * g = -(Complex.I • g) - c := by rw [hIg]; abel
  have e1 : (1 + Complex.I • a) * ((-Complex.I) • (a + b * g)) =
      (-Complex.I) • a + (-Complex.I) • (b * g) + a * a + a * b * g := by
    simp only [add_mul, one_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
      mul_assoc]
    simp only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    abel
  rw [e1, hab, neg_mul, mul_assoc, hdg, mul_sub, mul_neg, mul_smul_comm, ← h00]
  module

end Helpers

/-- LIB-1 (mQSP Eq. (5.35)). The Cayley junction: public `E`, private `Reg 2 E`,
`S = [[0, -i ⟨0|ₐ], [|0⟩ₐ, i (1 - Π)]]`. -/
noncomputable def cayley : Junction E (Reg 2 E) (onePort (Reg 2 E)) where
  S := DSum.block 0 ((-Complex.I) • Reg.proj 0) (Reg.single 0)
    (Complex.I • (1 - sigProj E))
  isUnitary_S := by
    rw [one_sub_sigProj]
    constructor <;>
    · rw [DSum.adjoint_block, DSum.block_comp_block, ← DSum.block_one_zero_zero_one,
        DSum.block_ext_iff]
      simp [ContinuousLinearMap.comp_assoc, map_smulₛₗ, ContinuousLinearMap.adjoint_comp,
        reg2_proj1_comp_single0, reg2_proj_single_comp_same, reg2_proj0_single1_comp,
        smul_smul, reg2_single_proj_add]
  ports := Ports.one (Reg 2 E)
  delay _ := 1
  one_le_delay _ := le_rfl

variable {E}

@[simp] theorem cayley_A : (cayley E).A = 0 := DSum.fst_block_inl _ _ _ _
@[simp] theorem cayley_B : (cayley E).B = (-Complex.I) • Reg.proj 0 := DSum.fst_block_inr _ _ _ _
@[simp] theorem cayley_C : (cayley E).C = Reg.single 0 := DSum.snd_block_inl _ _ _ _
@[simp] theorem cayley_D : (cayley E).D = Complex.I • (1 - sigProj E) :=
  DSum.snd_block_inr _ _ _ _

@[simp] theorem cayley_delay (i : One) : (cayley E).delay i = 1 := rfl
@[simp] theorem cayley_π (i : One) : (cayley E).ports.π i = 1 := rfl

theorem cayley_Q (O : Reg 2 E →L[ℂ] Reg 2 E) : (cayley E).Q (oneOracle O) = O := by
  rw [Q, Ports.feedback, Fintype.sum_unique]
  simp only [cayley_π, adjoint_one, one_comp, comp_one]
  rfl

/-- The encoded operator `A = ⟨0|ₐ O |0⟩ₐ` of a block encoding on `Reg 2 E`. -/
noncomputable abbrev encoded (O : Reg 2 E →L[ℂ] Reg 2 E) : E →L[ℂ] E :=
  Reg.proj 0 ∘L O ∘L Reg.single 0

/-- A self-inverse (reflection) block encoding: `O† = O`, `O O = 1`. -/
structure IsSelfInverse (O : Reg 2 E →L[ℂ] Reg 2 E) : Prop where
  adjoint_eq : O† = O
  mul_self : O ∘L O = 1

section SelfInverse

variable {O : Reg 2 E →L[ℂ] Reg 2 E}

/-- The `2×2` blocks `⟨a|ₐ O |b⟩ₐ` of a self-adjoint `O` satisfy `(O_ab)† = O_ba`. -/
theorem IsSelfInverse.adjoint_blk (hO : IsSelfInverse O) (a b : Fin 2) :
    (Reg.proj a ∘L O ∘L Reg.single b)† = Reg.proj b ∘L O ∘L Reg.single a := by
  simp [ContinuousLinearMap.adjoint_comp, hO.adjoint_eq, ContinuousLinearMap.comp_assoc]

/-- `O O = 1` in `2×2` blocks: `O_a0 O_0b + O_a1 O_1b = δ_ab`. -/
theorem IsSelfInverse.blk_mul (hO : IsSelfInverse O) (a b : Fin 2) :
    (Reg.proj a ∘L O ∘L Reg.single 0) ∘L (Reg.proj 0 ∘L O ∘L Reg.single b) +
      (Reg.proj a ∘L O ∘L Reg.single 1) ∘L (Reg.proj 1 ∘L O ∘L Reg.single b) =
      Reg.proj a ∘L Reg.single b := by
  have h : Reg.proj a ∘L O ∘L (Reg.single 0 ∘L Reg.proj 0 + Reg.single 1 ∘L Reg.proj 1) ∘L
      O ∘L Reg.single b = Reg.proj a ∘L Reg.single b := by
    rw [reg2_single_proj_add, one_comp, ← ContinuousLinearMap.comp_assoc O O, hO.mul_self,
      one_comp]
  rw [← h]
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc]

theorem IsSelfInverse.isIsometry (hO : IsSelfInverse O) : IsIsometry O := by
  rw [IsIsometry, hO.adjoint_eq, hO.mul_self]

end SelfInverse

/-- LIB-1 (mQSP Eq. (1.25)). The steady state of the Cayley loop is regular for every
self-inverse block encoding, and `1 + i A` is invertible on the public space. -/
theorem cayley_isRegular {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    (cayley E).IsRegular (oneOracle O) := by
  rw [isRegular_iff_injective, cayley_D, cayley_Q, one_sub_sigProj, injective_iff_map_eq_zero]
  intro v hv
  simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, smul_apply] at hv
  have hv' : v = Complex.I • Reg.single 1 (Reg.proj 1 (O v)) := sub_eq_zero.1 hv
  have h0 : Reg.proj 0 v = 0 := by
    rw [hv', map_smul, Reg.proj_single_of_ne (by decide), smul_zero]
  have hvw : v = Reg.single 1 (Reg.proj 1 v) := by
    conv_lhs => rw [← reg2_decomp v]
    rw [h0, map_zero, zero_add]
  have hw : Reg.proj 1 v = 0 := by
    have h1 : Reg.proj 1 v = Complex.I • Reg.proj 1 (O (Reg.single 1 (Reg.proj 1 v))) := by
      conv_lhs => rw [hv']
      rw [map_smul, Reg.proj_single_same, ← hvw]
    refine eq_zero_of_apply_eq_smul (hO.adjoint_blk 1 1) conj_neg_I_ne ?_
    simp only [ContinuousLinearMap.comp_apply]
    conv_rhs => rw [h1]
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  rw [hvw, hw, map_zero]

theorem isUnit_one_add_I_smul_encoded {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    IsUnit (1 + Complex.I • encoded O) := by
  have hinj : Function.Injective ⇑(1 + Complex.I • encoded O) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    simp only [add_apply, one_apply_eq_self, smul_apply] at hv
    refine eq_zero_of_apply_eq_smul (hO.adjoint_blk 0 0) conj_I_ne ?_
    have h1 : Complex.I • encoded O v = -v := eq_neg_of_add_eq_zero_right hv
    calc encoded O v = (-Complex.I) • (Complex.I • encoded O v) := by
          rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      _ = Complex.I • v := by rw [h1, smul_neg, neg_smul, neg_neg]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- The catalyst of the Cayley loop is `Γ = |0⟩ₐ + |1⟩ₐ G` with `G = i (O₁₀ + O₁₁ G)`. -/
theorem cayley_catalyst_decomp {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    ∃ G : E →L[ℂ] E, (cayley E).catalyst (oneOracle O) = Reg.single 0 + Reg.single 1 ∘L G ∧
      G = Complex.I • (Reg.proj 1 ∘L O ∘L Reg.single 0 +
        (Reg.proj 1 ∘L O ∘L Reg.single 1) ∘L G) := by
  have hfix := (cayley E).catalyst_eq (cayley_isRegular hO)
  rw [cayley_C, cayley_D, cayley_Q, one_sub_sigProj] at hfix
  generalize (cayley E).catalyst (oneOracle O) = Γ at hfix ⊢
  have h0 : Reg.proj 0 ∘L Γ = 1 := by
    rw [hfix]
    simp [ContinuousLinearMap.comp_assoc, reg2_proj0_single1_comp]
  have hΓ : Γ = Reg.single 0 + Reg.single 1 ∘L (Reg.proj 1 ∘L Γ) := by
    conv_lhs => rw [← one_comp Γ, ← reg2_single_proj_add]
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, h0, comp_one,
      ContinuousLinearMap.comp_assoc]
  refine ⟨Reg.proj 1 ∘L Γ, hΓ, ?_⟩
  have h1 : Reg.proj 1 ∘L Γ = Complex.I • (Reg.proj 1 ∘L O ∘L Γ) := by
    conv_lhs => rw [hfix]
    simp [ContinuousLinearMap.comp_assoc, reg2_proj1_comp_single0, reg2_proj_single_comp_same]
  conv_lhs => rw [h1, hΓ]
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_assoc]

/-- LIB-1 (mQSP Eq. (1.31)). The steady value of the Cayley module is the Cayley transform
`(1 - i A)(1 + i A)⁻¹` of the encoded Hermitian contraction `A = ⟨0|ₐ O |0⟩ₐ`. -/
theorem cayley_steady {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    (cayley E).steady (oneOracle O) =
      (1 - Complex.I • encoded O) ∘L Ring.inverse (1 + Complex.I • encoded O) := by
  obtain ⟨G, hΓ, hG⟩ := cayley_catalyst_decomp hO
  have hF : (cayley E).steady (oneOracle O) =
      (-Complex.I) • (encoded O + (Reg.proj 0 ∘L O ∘L Reg.single 1) ∘L G) := by
    rw [steady, cayley_A, cayley_B, cayley_Q, hΓ]
    simp only [zero_add, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_assoc, smul_add]
  have key : (1 + Complex.I • encoded O) * (cayley E).steady (oneOracle O) =
      1 - Complex.I • encoded O := by
    rw [hF]
    refine cayley_alg (c := Reg.proj 1 ∘L O ∘L Reg.single 0)
      (d := Reg.proj 1 ∘L O ∘L Reg.single 1) ?_ ?_ hG
    · have h := hO.blk_mul 0 0
      rw [reg2_proj_comp_single_same] at h
      exact h
    · have h := hO.blk_mul 0 1
      rw [reg2_proj0_comp_single1] at h
      exact h
  obtain ⟨u, hu⟩ := isUnit_one_add_I_smul_encoded hO
  have hcomm : Commute (1 - Complex.I • encoded O) (u : E →L[ℂ] E) := by
    rw [hu]
    change (1 - Complex.I • encoded O) * (1 + Complex.I • encoded O) =
      (1 + Complex.I • encoded O) * (1 - Complex.I • encoded O)
    simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm]
    module
  rw [← hu] at key
  rw [← hu, Ring.inverse_unit, ← ContinuousLinearMap.mul_def, hcomm.units_inv_right.eq, ← key,
    Units.inv_mul_cancel_left]

/-- LIB-1 (mQSP Eq. (1.27)). On a unit eigenvector `ψ` of `A` with real eigenvalue `x`, the
catalyst weight of the Cayley module is `2/(1 + x²)`. -/
theorem cayley_weight_eigen {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) {ψ : E}
    (hψ : ‖ψ‖ = 1) {x : ℝ} (hx : encoded O ψ = (x : ℂ) • ψ) :
    (cayley E).weight (oneOracle O) () ψ = 2 / (1 + x ^ 2) := by
  obtain ⟨G, hΓ, hG⟩ := cayley_catalyst_decomp hO
  rw [weight, cayley_π, one_apply_eq_self, hΓ, add_apply,
    ContinuousLinearMap.comp_apply, reg2_norm_sq_single_add, hψ]
  simp only [ContinuousLinearMap.comp_apply] at hx
  set φ := Reg.proj 1 (O (Reg.single 0 ψ)) with hφdef
  -- `O (|0⟩ ψ) = |0⟩ (x ψ) + |1⟩ φ`, hence `O₁₁ φ = -x φ` and `‖φ‖² = 1 - x²`.
  have hOs : O (Reg.single 0 ψ) = Reg.single 0 ((x : ℂ) • ψ) + Reg.single 1 φ := by
    rw [← hx, hφdef, reg2_decomp]
  have hdφ : Reg.proj 1 (O (Reg.single 1 φ)) = -((x : ℂ) • φ) := by
    have h := congrArg (fun v => Reg.proj 1 (O v)) hOs
    have hOO : O (O (Reg.single 0 ψ)) = Reg.single 0 ψ := by
      rw [← ContinuousLinearMap.comp_apply, hO.mul_self, one_apply_eq_self]
    rw [hOO, Reg.proj_single_of_ne (by decide), map_add, map_add, map_smul, map_smul,
      map_smul, ← hφdef] at h
    rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
  have hφ : ‖φ‖ ^ 2 = 1 - x ^ 2 := by
    have h := Reg.norm_sq_eq (O (Reg.single 0 ψ))
    rw [Fin.sum_univ_two, hO.isIsometry.norm_map, (Reg.isIsometry_single 0).norm_map, hψ, hx,
      norm_smul, ← hφdef, hψ, Complex.norm_real, Real.norm_eq_abs, mul_one, sq_abs] at h
    linarith
  -- `G ψ = (x - i)⁻¹ φ`.
  have hxI : (x : ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  set c : ℂ := ((x : ℂ) - Complex.I)⁻¹ with hcdef
  have hc : c * ((x : ℂ) - Complex.I) = 1 := inv_mul_cancel₀ hxI
  have hGψ : G ψ = Complex.I • (φ + Reg.proj 1 (O (Reg.single 1 (G ψ)))) := by
    conv_lhs => rw [hG]
    rfl
  have hq : Reg.proj 1 (O (Reg.single 1 (G ψ))) = (-Complex.I) • G ψ - φ := by
    conv_rhs => rw [hGψ]
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    abel
  have hu : G ψ - c • φ = 0 := by
    refine eq_zero_of_apply_eq_smul (hO.adjoint_blk 1 1) conj_neg_I_ne ?_
    simp only [ContinuousLinearMap.comp_apply, map_sub, map_smul, hdφ]
    linear_combination (norm := module) hq + hc • φ
  rw [sub_eq_zero.1 hu, norm_smul, mul_pow, hφ, hcdef, norm_inv, inv_pow, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im,
    Complex.ofReal_im, Complex.I_im, zero_sub]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  field_simp
  ring

end Junction

end MQSP
