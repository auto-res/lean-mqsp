/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.BlockEncoding

/-!
# Post-compilation operations on encodings (RES-2; mQSP Lemmas A.2, A.3, A.4)

* **Normalization and approximation error** (Lemma A.2): an encoding of `A/(1+η)` with
  `‖A - G‖ ≤ ξ` is also an encoding of `G̃/(1+δ)` for any `0 < δ ≤ η`, where
  `G̃ = (1+δ)/(1+η) · A` satisfies `‖G̃ - G‖ ≤ η - δ + ξ`.
* **Conditioning an approximate output vector** (Lemma A.3): if `‖x̃ - x‖ ≤ E < ‖x‖` then the
  normalised vectors satisfy `‖x̃/‖x̃‖ - x/‖x‖‖ ≤ 2E/‖x‖`.
* **Oblivious amplitude amplification** (Lemma A.4, [BCC+15]): if the unitary `A` encodes
  `G̃/2` between the isometry `V`, then with `R = 2 V V† - 1`, the unitary `-A R A† R A`
  encodes `(3 G̃ - G̃ G̃† G̃)/2` (Eq. (A.9)) using two forward and one inverse execution; when
  `‖G̃ - G‖ ≤ δ` for a unitary `G`, the encoded operator is within `δ + (3δ² + δ³)/2` of `G`.
-/

namespace MQSP

universe u v

open scoped InnerProductSpace

namespace Resource

variable {H : Type u} {P : Type v} [HSpace H] [HSpace P]

/-- RES-2 (mQSP Lemma A.2). Rescaling the encoded block: an encoding of `A/(1+η)` is an
encoding of `((1+δ)/(1+η)) A / (1+δ)`, and the rescaled operator stays close to `G`. -/
theorem isEncodingOf_rescale {U : H →L[ℂ] H} {Vin Vout : P →L[ℂ] H} {A G : P →L[ℂ] P}
    {η δ ξ : ℝ} (hδ : 0 ≤ δ) (hδη : δ ≤ η)
    (h : IsEncodingOf U Vin Vout (((1 + η : ℝ)⁻¹ : ℂ) • A)) (hAG : ‖A - G‖ ≤ ξ) (hG : ‖G‖ ≤ 1) :
    IsEncodingOf U Vin Vout (((1 + δ : ℝ)⁻¹ : ℂ) • ((((1 + δ) / (1 + η) : ℝ) : ℂ) • A)) ∧
      ‖(((1 + δ) / (1 + η) : ℝ) : ℂ) • A - G‖ ≤ η - δ + ξ := by
  have hη : 0 < 1 + η := by linarith
  have hδ' : 0 < 1 + δ := by linarith
  have hs : ((1 + δ : ℝ)⁻¹ : ℂ) * (((1 + δ) / (1 + η) : ℝ) : ℂ) = ((1 + η : ℝ)⁻¹ : ℂ) := by
    have h1 : ((1 + δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hδ'.ne'
    have h2 : ((1 + η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    push_cast at h1 h2 ⊢
    field_simp
  refine ⟨by rw [smul_smul, hs]; exact h, ?_⟩
  set c : ℝ := (1 + δ) / (1 + η) with hc
  have hc0 : 0 ≤ c := div_nonneg hδ'.le hη.le
  have hc1 : c ≤ 1 := (div_le_one hη).2 (by linarith)
  have h1c : 1 - c ≤ η - δ := by
    have : 1 - c = (η - δ) / (1 + η) := by rw [hc]; field_simp; ring
    rw [this, div_le_iff₀ hη]
    nlinarith
  have hξ : 0 ≤ ξ := (norm_nonneg _).trans hAG
  calc ‖(c : ℂ) • A - G‖ = ‖(c : ℂ) • (A - G) - ((1 - c : ℝ) : ℂ) • G‖ := by
        congr 1
        rw [smul_sub, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        abel
    _ ≤ ‖(c : ℂ) • (A - G)‖ + ‖((1 - c : ℝ) : ℂ) • G‖ := norm_sub_le _ _
    _ = c * ‖A - G‖ + (1 - c) * ‖G‖ := by
        rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc0,
          Real.norm_of_nonneg (by linarith)]
    _ ≤ 1 * ξ + (η - δ) * 1 := by gcongr
    _ = η - δ + ξ := by ring

/-- RES-2 (mQSP Lemma A.3). Conditioning: normalising an approximate vector. -/
theorem norm_normalize_sub_normalize_le {x xt : P} {E : ℝ} (hE : ‖xt - x‖ ≤ E) (hx : E < ‖x‖) :
    ‖(‖xt‖⁻¹ : ℂ) • xt - (‖x‖⁻¹ : ℂ) • x‖ ≤ 2 * E / ‖x‖ := by
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hβ : 0 < ‖x‖ := hE0.trans_lt hx
  have hdiff : |‖x‖ - ‖xt‖| ≤ ‖xt - x‖ := by
    rw [norm_sub_rev]; exact abs_norm_sub_norm_le x xt
  have hb : 0 < ‖xt‖ := by
    have := (abs_le.1 hdiff).2
    linarith
  have key : (‖xt‖⁻¹ : ℂ) • xt - (‖x‖⁻¹ : ℂ) • x
      = (‖x‖⁻¹ : ℂ) • (xt - x) + ((‖xt‖⁻¹ - ‖x‖⁻¹ : ℝ) : ℂ) • xt := by
    push_cast
    rw [smul_sub, sub_smul]
    abel
  have hsc : |‖xt‖⁻¹ - ‖x‖⁻¹| * ‖xt‖ = |‖x‖ - ‖xt‖| / ‖x‖ := by
    have : (‖xt‖⁻¹ - ‖x‖⁻¹) * ‖xt‖ = (‖x‖ - ‖xt‖) / ‖x‖ := by
      field_simp
    rw [show |‖xt‖⁻¹ - ‖x‖⁻¹| * ‖xt‖ = |(‖xt‖⁻¹ - ‖x‖⁻¹) * ‖xt‖| by
      rw [abs_mul, abs_of_pos hb], this, abs_div, abs_of_pos hβ]
  rw [key]
  calc _ ≤ ‖(‖x‖⁻¹ : ℂ) • (xt - x)‖ + ‖((‖xt‖⁻¹ - ‖x‖⁻¹ : ℝ) : ℂ) • xt‖ := norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖xt - x‖ + |‖xt‖⁻¹ - ‖x‖⁻¹| * ‖xt‖ := by
        rw [norm_smul, norm_smul, norm_inv, Complex.norm_real, Complex.norm_real, norm_norm,
          Real.norm_eq_abs]
    _ = (‖xt - x‖ + |‖x‖ - ‖xt‖|) / ‖x‖ := by rw [hsc, inv_mul_eq_div, add_div]
    _ ≤ 2 * E / ‖x‖ := by
        gcongr
        linarith

/-- The reflection about the selected sector of an isometry `V`: `2 V V† - 1`. -/
noncomputable def sectorReflection (V : P →L[ℂ] H) : H →L[ℂ] H := reflection (V ∘L V†)

theorem isProj_comp_adjoint {V : P →L[ℂ] H} (hV : IsIsometry V) : IsProj (V ∘L V†) := by
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  · calc (V ∘L V†) ∘L (V ∘L V†) = V ∘L (V† ∘L V) ∘L V† := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = V ∘L V† := by rw [hV, one_comp]

theorem isUnitary_neg {E : Type*} [HSpace E] {U : E →L[ℂ] E} (h : IsUnitary U) :
    IsUnitary (-U) := by
  refine ⟨?_, ?_⟩ <;>
    simp only [map_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, neg_neg,
      h.1, h.2]

/-- RES-2 (mQSP Lemma A.4, Eq. (A.9)). Oblivious amplitude amplification: if `A` encodes `X`
between the isometry `V` (on both sides), then `-A R A† R A` encodes `3X - 4 X X† X`. -/
theorem oaa_block {A : H →L[ℂ] H} {V : P →L[ℂ] H} {X : P →L[ℂ] P} (h : IsEncodingOf A V V X) :
    IsEncodingOf (-(A ∘L sectorReflection V ∘L A† ∘L sectorReflection V ∘L A)) V V
      ((3 : ℂ) • X - (4 : ℂ) • (X ∘L X† ∘L X)) := by
  have hR : IsUnitary (sectorReflection V) :=
    (isProj_comp_adjoint h.isIsometry_in).reflection_isUnitary
  have hA := h.isUnitary
  refine ⟨isUnitary_neg (hA.comp (hR.comp (hA.adjoint.comp (hR.comp hA)))), h.isIsometry_in,
    h.isIsometry_in, ?_⟩
  have hX : ∀ y, V† (A (V y)) = X y := fun y => by rw [← h.block]; rfl
  have hXa : ∀ y, V† (A† (V y)) = X† y := fun y => by
    rw [← h.block, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
    rfl
  have hAA : ∀ y, A† (A y) = y := hA.isIsometry.apply_adjoint_apply
  have hAA' : ∀ y, A (A† y) = y := fun y => by
    have := congrArg (fun T : H →L[ℂ] H => T y) hA.2
    simpa using this
  have hVV : ∀ y, V† (V y) = y := h.isIsometry_in.apply_adjoint_apply
  have hRy : ∀ y, sectorReflection V y = (2 : ℂ) • V (V† y) - y := fun y => by
    simp [sectorReflection, reflection]
  ext x
  simp only [ContinuousLinearMap.comp_apply, neg_apply, hRy, map_sub,
    map_smul, map_neg, hX, hXa, hAA, hAA', hVV, sub_apply, smul_apply]
  module

/-- With `X = G̃/2`, the amplified block is `(3G̃ - G̃G̃†G̃)/2`. -/
theorem oaa_block_half {A : H →L[ℂ] H} {V : P →L[ℂ] H} {Gt : P →L[ℂ] P}
    (h : IsEncodingOf A V V ((2 : ℂ)⁻¹ • Gt)) :
    IsEncodingOf (-(A ∘L sectorReflection V ∘L A† ∘L sectorReflection V ∘L A)) V V
      ((2 : ℂ)⁻¹ • ((3 : ℂ) • Gt - Gt ∘L Gt† ∘L Gt)) := by
  have h' := oaa_block h
  have heq : (3 : ℂ) • ((2 : ℂ)⁻¹ • Gt) - (4 : ℂ) • (((2 : ℂ)⁻¹ • Gt) ∘L ((2 : ℂ)⁻¹ • Gt)† ∘L
      ((2 : ℂ)⁻¹ • Gt)) = (2 : ℂ)⁻¹ • ((3 : ℂ) • Gt - Gt ∘L Gt† ∘L Gt) := by
    rw [map_smulₛₗ]
    simp only [map_inv₀, map_ofNat, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      smul_smul]
    module
  exact ⟨h'.isUnitary, h'.isIsometry_in, h'.isIsometry_out, h'.block.trans heq⟩

/-- RES-2 (error of oblivious amplitude amplification, crude form). If `G` is unitary and
`‖G̃ - G‖ ≤ δ` then `‖(3G̃ - G̃G̃†G̃)/2 - G‖ ≤ δ + (3δ² + δ³)/2`. -/
theorem norm_oaa_sub_le {Gt G : P →L[ℂ] P} (hG : IsUnitary G) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ‖Gt - G‖ ≤ δ) :
    ‖(2 : ℂ)⁻¹ • ((3 : ℂ) • Gt - Gt ∘L Gt† ∘L Gt) - G‖ ≤ δ + (3 * δ ^ 2 + δ ^ 3) / 2 := by
  have _ := hδ
  obtain ⟨E, rfl⟩ : ∃ E, Gt = G + E := ⟨Gt - G, by abel⟩
  have hE : ‖E‖ ≤ δ := by simpa using h
  have hu1 : star G * G = 1 := by rw [ContinuousLinearMap.star_eq_adjoint]; exact hG.1
  have hu2 : G * star G = 1 := by rw [ContinuousLinearMap.star_eq_adjoint]; exact hG.2
  set W : P →L[ℂ] P := E - G * star E * G - G * star E * E - E * star G * E - E * star E * G -
    E * star E * E with hW
  have key : (3 : ℂ) • (G + E) - (G + E) * (star (G + E) * (G + E)) = (2 : ℂ) • G + W := by
    have hd : (G + E) * ((star G + star E) * (G + E)) = G * star G * G + G * star G * E +
        E * (star G * G) + (G * star E * G + G * star E * E + E * star G * E + E * star E * G +
          E * star E * E) := by
      noncomm_ring
    rw [hu1, hu2, one_mul, one_mul, mul_one] at hd
    rw [star_add, hd, hW]
    module
  have hrw : (G + E) ∘L (G + E)† ∘L (G + E) = (G + E) * (star (G + E) * (G + E)) := by
    rw [ContinuousLinearMap.star_eq_adjoint]; rfl
  rw [hrw, key, smul_add, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, add_sub_cancel_left,
    norm_smul, norm_inv, Complex.norm_ofNat]
  have hEs : ‖star E‖ ≤ δ := by
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]; exact hE
  have hGn : ‖G‖ ≤ 1 := hG.opNorm_le_one
  have hGs : ‖star G‖ ≤ 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]; exact hGn
  have t : ∀ a b c : P →L[ℂ] P, ∀ x y z : ℝ, ‖a‖ ≤ x → ‖b‖ ≤ y → ‖c‖ ≤ z →
      ‖a * b * c‖ ≤ x * y * z := fun a b c x y z ha hb hc =>
    norm_mul₃_le.trans (mul_le_mul (mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha))
      hc (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans ha) ((norm_nonneg _).trans hb)))
  have b1 := t G (star E) G 1 δ 1 hGn hEs hGn
  have b2 := t G (star E) E 1 δ δ hGn hEs hE
  have b3 := t E (star G) E δ 1 δ hE hGs hE
  have b4 := t E (star E) G δ δ 1 hE hEs hGn
  have b5 := t E (star E) E δ δ δ hE hEs hE
  have n1 := norm_sub_le E (G * star E * G)
  have n2 := norm_sub_le (E - G * star E * G) (G * star E * E)
  have n3 := norm_sub_le (E - G * star E * G - G * star E * E) (E * star G * E)
  have n4 := norm_sub_le (E - G * star E * G - G * star E * E - E * star G * E) (E * star E * G)
  have n5 := norm_sub_le (E - G * star E * G - G * star E * E - E * star G * E - E * star E * G)
    (E * star E * E)
  rw [← hW] at n5
  nlinarith

end Resource

end MQSP
