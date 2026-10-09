/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg

/-!
# Approximate implementations, stitching and uncomputation (CPE-0, CPE-3; Rall Lemmas 3, 7, 8)

The vector-level specification language of coherent estimation:

* `ApproxImpl ε M W S`: the unitary `M` implements `W` within `ε` on the input subspace `S`
  with clean ancilla: `‖M (ψ ⊕ 0) - (W ψ) ⊕ 0‖ ≤ ε ‖ψ‖` for `ψ ∈ S` (ancilla modelled as the
  second summand of a direct sum; `0` ancilla state `= inl ψ`);
* **stitching** (Rall Lemma 7): if `M₁` implements `W₁` within `ε₁` on `S` and `M₂` implements
  `W₂` within `ε₂` on `W₁ '' S`, then `M₂ M₁` implements `W₂ W₁` within `ε₁ + ε₂` on `S`
  (hybrid argument; errors add along the chain, giving the geometric budget `δ 2^{-k-1}`
  per bit);
* **uncomputation** (Rall Lemmas 3/8, pure-state version): if `M` implements the map
  `ψ ↦ (estimate(ψ)) ⊗ ψ` with garbage, then `copy ∘ M⁻¹ ∘ … ` returns the estimate with clean
  garbage within `2ε`; here in the form: running `M`, copying the output register and running
  `M†` yields `W` within `2 ε`.
-/

namespace MQSP

universe u v

open scoped InnerProductSpace

namespace CPE

variable {H : Type u} [HSpace H]

/-- CPE-0. `M` implements `W` within `ε` on the subspace `S` (clean ancilla: the second summand
of `H ⊕ₕ A` is the ancilla, initialised and returned to `0`). -/
def ApproxImpl {A : Type v} [HSpace A] (ε : ℝ) (M : H ⊕ₕ A →L[ℂ] H ⊕ₕ A) (W : H →L[ℂ] H)
    (S : Set H) : Prop :=
  ∀ ψ ∈ S, ‖M (DSum.inl ψ) - DSum.inl (W ψ)‖ ≤ ε * ‖ψ‖

/-- An exact implementation is approximate with `ε = 0`. -/
theorem approxImpl_of_exact {A : Type v} [HSpace A] {M : H ⊕ₕ A →L[ℂ] H ⊕ₕ A} {W : H →L[ℂ] H}
    (h : ∀ ψ, M (DSum.inl ψ) = DSum.inl (W ψ)) (S : Set H) : ApproxImpl 0 M W S := by
  intro ψ _
  rw [h ψ, sub_self, norm_zero, zero_mul]

/-- Monotonicity in `ε` and in the subspace. -/
theorem ApproxImpl.mono {A : Type v} [HSpace A] {ε ε' : ℝ} {M : H ⊕ₕ A →L[ℂ] H ⊕ₕ A}
    {W : H →L[ℂ] H} {S S' : Set H} (h : ApproxImpl ε M W S) (hε : ε ≤ ε') (hS : S' ⊆ S) :
    ApproxImpl ε' M W S' := by
  intro ψ hψ
  exact le_trans (h ψ (hS hψ)) (mul_le_mul_of_nonneg_right hε (norm_nonneg _))

/-- CPE-3 (Rall Lemma 7, stitching). Approximate implementations compose along a chain with
additive error, provided the second holds on the image of the first and `M₂` is unitary. -/
theorem ApproxImpl.comp {A : Type v} [HSpace A] {ε₁ ε₂ : ℝ} {M₁ M₂ : H ⊕ₕ A →L[ℂ] H ⊕ₕ A}
    {W₁ W₂ : H →L[ℂ] H} {S : Set H} (h₁ : ApproxImpl ε₁ M₁ W₁ S)
    (h₂ : ApproxImpl ε₂ M₂ W₂ (W₁ '' S)) (hM₂ : IsUnitary M₂) (hW₁ : IsIsometry W₁) :
    ApproxImpl (ε₁ + ε₂) (M₂ ∘L M₁) (W₂ ∘L W₁) S := by
  intro ψ hψ
  have hdecomp : (M₂ ∘L M₁) (DSum.inl ψ) - DSum.inl ((W₂ ∘L W₁) ψ) =
      M₂ (M₁ (DSum.inl ψ) - DSum.inl (W₁ ψ)) + (M₂ (DSum.inl (W₁ ψ)) - DSum.inl (W₂ (W₁ ψ))) := by
    rw [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      sub_add_sub_cancel]
  have e₁ : ‖M₂ (M₁ (DSum.inl ψ) - DSum.inl (W₁ ψ))‖ ≤ ε₁ * ‖ψ‖ :=
    calc ‖M₂ (M₁ (DSum.inl ψ) - DSum.inl (W₁ ψ))‖
        = ‖M₁ (DSum.inl ψ) - DSum.inl (W₁ ψ)‖ := hM₂.isIsometry.norm_map _
      _ ≤ ε₁ * ‖ψ‖ := h₁ ψ hψ
  have e₂ : ‖M₂ (DSum.inl (W₁ ψ)) - DSum.inl (W₂ (W₁ ψ))‖ ≤ ε₂ * ‖ψ‖ := by
    have := h₂ (W₁ ψ) ⟨ψ, hψ, rfl⟩
    rwa [hW₁.norm_map] at this
  rw [hdecomp, add_mul]
  exact le_trans (norm_add_le _ _) (add_le_add e₁ e₂)

/-- Approximate implementations transfer along operator-norm closeness of the targets. -/
theorem ApproxImpl.of_norm_sub_le {A : Type v} [HSpace A] {ε η : ℝ} {M : H ⊕ₕ A →L[ℂ] H ⊕ₕ A}
    {W W' : H →L[ℂ] H} {S : Set H} (h : ApproxImpl ε M W S) (hW : ‖W - W'‖ ≤ η) :
    ApproxImpl (ε + η) M W' S := by
  intro ψ hψ
  have hdecomp : M (DSum.inl ψ) - DSum.inl (W' ψ) =
      (M (DSum.inl ψ) - DSum.inl (W ψ)) + DSum.inl ((W - W') ψ) := by
    rw [sub_apply, map_sub, sub_add_sub_cancel]
  have e : ‖(DSum.inl ((W - W') ψ) : H ⊕ₕ A)‖ ≤ η * ‖ψ‖ := by
    rw [DSum.norm_inl]
    exact le_trans ((W - W').le_opNorm ψ) (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
  rw [hdecomp, add_mul]
  exact le_trans (norm_add_le _ _) (add_le_add (h ψ hψ) e)

/-- CPE-3 (Rall Lemma 3/8, pure-state uncomputation). If `M` implements `W` within `ε` and
`M` is unitary then `M†` implements `W†` within `ε` on the image `W '' S`, hence
`M† ∘ M` implements `1` within `2ε`: the garbage produced by `M` is removed by running it
backwards. -/
theorem ApproxImpl.adjoint {A : Type v} [HSpace A] {ε : ℝ} {M : H ⊕ₕ A →L[ℂ] H ⊕ₕ A}
    {W : H →L[ℂ] H} {S : Set H} (h : ApproxImpl ε M W S) (hM : IsUnitary M) (hW : IsUnitary W) :
    ApproxImpl ε (M†) (W†) (W '' S) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  have hinl : M† (M (DSum.inl ψ)) = DSum.inl ψ := hM.isIsometry.apply_adjoint_apply _
  have hdecomp : M† (DSum.inl (W ψ)) - DSum.inl (W† (W ψ)) =
      M† (DSum.inl (W ψ) - M (DSum.inl ψ)) := by
    rw [hW.isIsometry.apply_adjoint_apply, map_sub, hinl]
  rw [hdecomp, hM.adjoint.isIsometry.norm_map, norm_sub_rev, hW.isIsometry.norm_map]
  exact h ψ hψ

theorem ApproxImpl.uncompute {A : Type v} [HSpace A] {ε : ℝ} {M : H ⊕ₕ A →L[ℂ] H ⊕ₕ A}
    {W : H →L[ℂ] H} {S : Set H} (h : ApproxImpl ε M W S) (hM : IsUnitary M) (hW : IsUnitary W) :
    ApproxImpl (ε + ε) (M† ∘L M) 1 S := by
  have h' := h.comp (h.adjoint hM hW) hM.adjoint hW.isIsometry
  rwa [hW.1] at h'

end CPE

end MQSP
