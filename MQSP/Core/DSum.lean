/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.HSpace

/-!
# Direct sums and block operators (CORE-2)

The Hilbert-space direct sum `P ⊕ₕ L = WithLp 2 (P × L)` carries the injections `inl`, `inr`
and projections `fst`, `snd` (bounded operators), with `inl† = fst`, `inr† = snd`,
`fst ∘ inl = 1`, `inl ∘ fst + inr ∘ snd = 1`.

An operator `P ⊕ₕ L →L[ℂ] P' ⊕ₕ L'` is a `2×2` block operator
`block A B C D = [[A, B], [C, D]]` (mQSP system matrix `S = (A B; C D)`, public first).
This file proves the block algebra (composition, adjoint, identity, extensionality) and the
block characterisation of unitarity.
-/

namespace MQSP

universe u v u' v'

open scoped InnerProductSpace

namespace DSum

variable {P : Type u} {L : Type v} [HSpace P] [HSpace L]

/-- Injection of the public summand: `inl x = (x, 0)`. -/
noncomputable def inl : P →L[ℂ] P ⊕ₕ L :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ P L).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ P L

/-- Injection of the private summand: `inr y = (0, y)`. -/
noncomputable def inr : L →L[ℂ] P ⊕ₕ L :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ P L).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ P L

/-- Projection onto the public summand. -/
noncomputable def fst : P ⊕ₕ L →L[ℂ] P :=
  ContinuousLinearMap.fst ℂ P L ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ P L).toContinuousLinearMap

/-- Projection onto the private summand. -/
noncomputable def snd : P ⊕ₕ L →L[ℂ] L :=
  ContinuousLinearMap.snd ℂ P L ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ P L).toContinuousLinearMap

/-- Pair a public and a private vector. -/
noncomputable abbrev mk (x : P) (y : L) : P ⊕ₕ L := WithLp.toLp 2 (x, y)

@[simp] theorem inl_apply (x : P) : (inl x : P ⊕ₕ L) = mk x 0 := rfl
@[simp] theorem inr_apply (y : L) : (inr y : P ⊕ₕ L) = mk 0 y := rfl
theorem fst_apply (v : P ⊕ₕ L) : fst v = v.ofLp.1 := rfl
theorem snd_apply (v : P ⊕ₕ L) : snd v = v.ofLp.2 := rfl
@[simp] theorem fst_mk (x : P) (y : L) : fst (mk x y) = x := rfl
@[simp] theorem snd_mk (x : P) (y : L) : snd (mk x y) = y := rfl

@[ext] theorem ext {v w : P ⊕ₕ L} (h1 : fst v = fst w) (h2 : snd v = snd w) : v = w := by
  rcases v with ⟨v1, v2⟩; rcases w with ⟨w1, w2⟩
  simp only [fst_apply, snd_apply] at h1 h2
  rw [h1, h2]

theorem mk_fst_snd (v : P ⊕ₕ L) : mk (fst v) (snd v) = v := rfl

@[simp] theorem mk_add (x x' : P) (y y' : L) : mk (x + x') (y + y') = mk x y + mk x' y' := rfl
@[simp] theorem mk_smul (c : ℂ) (x : P) (y : L) : mk (c • x) (c • y) = c • mk x y := rfl
@[simp] theorem mk_zero : (mk 0 0 : P ⊕ₕ L) = 0 := rfl

theorem mk_eq_inl_add_inr (x : P) (y : L) : mk x y = inl x + inr y := by
  ext <;> simp

@[simp] theorem fst_comp_inl : fst ∘L (inl : P →L[ℂ] P ⊕ₕ L) = 1 := by
  ext x; simp
@[simp] theorem snd_comp_inl : snd ∘L (inl : P →L[ℂ] P ⊕ₕ L) = 0 := by
  ext x; simp
@[simp] theorem fst_comp_inr : fst ∘L (inr : L →L[ℂ] P ⊕ₕ L) = 0 := by
  ext x; simp
@[simp] theorem snd_comp_inr : snd ∘L (inr : L →L[ℂ] P ⊕ₕ L) = 1 := by
  ext x; simp

theorem inl_fst_add_inr_snd : inl ∘L fst + inr ∘L snd = (1 : P ⊕ₕ L →L[ℂ] P ⊕ₕ L) := by
  ext v <;> simp

theorem inner_mk_mk (x x' : P) (y y' : L) :
    ⟪(mk x y : P ⊕ₕ L), mk x' y'⟫_ℂ = ⟪x, x'⟫_ℂ + ⟪y, y'⟫_ℂ :=
  WithLp.prod_inner_apply _ _

theorem inner_inl_left (x : P) (v : P ⊕ₕ L) : ⟪inl x, v⟫_ℂ = ⟪x, fst v⟫_ℂ := by
  rw [inl_apply, ← mk_fst_snd v, inner_mk_mk]; simp
theorem inner_inr_left (y : L) (v : P ⊕ₕ L) : ⟪inr y, v⟫_ℂ = ⟪y, snd v⟫_ℂ := by
  rw [inr_apply, ← mk_fst_snd v, inner_mk_mk]; simp

@[simp] theorem adjoint_inl : (inl : P →L[ℂ] P ⊕ₕ L)† = fst := by
  symm; rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v x
  rw [← inner_conj_symm v (inl x), inner_inl_left, inner_conj_symm]
@[simp] theorem adjoint_inr : (inr : L →L[ℂ] P ⊕ₕ L)† = snd := by
  symm; rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v y
  rw [← inner_conj_symm v (inr y), inner_inr_left, inner_conj_symm]
@[simp] theorem adjoint_fst : (fst : P ⊕ₕ L →L[ℂ] P)† = inl := by
  rw [← adjoint_inl, ContinuousLinearMap.adjoint_adjoint]
@[simp] theorem adjoint_snd : (snd : P ⊕ₕ L →L[ℂ] L)† = inr := by
  rw [← adjoint_inr, ContinuousLinearMap.adjoint_adjoint]

theorem norm_sq_eq (v : P ⊕ₕ L) : ‖v‖ ^ 2 = ‖fst v‖ ^ 2 + ‖snd v‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 v

theorem norm_inl (x : P) : ‖(inl x : P ⊕ₕ L)‖ = ‖x‖ := by
  have h := norm_sq_eq (inl x : P ⊕ₕ L)
  simp only [inl_apply, fst_mk, snd_mk, norm_zero, zero_pow two_ne_zero, add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem norm_inr (y : L) : ‖(inr y : P ⊕ₕ L)‖ = ‖y‖ := by
  have h := norm_sq_eq (inr y : P ⊕ₕ L)
  simp only [inr_apply, fst_mk, snd_mk, norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem isIsometry_inl : IsIsometry (inl : P →L[ℂ] P ⊕ₕ L) := by
  rw [IsIsometry, adjoint_inl, fst_comp_inl]
theorem isIsometry_inr : IsIsometry (inr : L →L[ℂ] P ⊕ₕ L) := by
  rw [IsIsometry, adjoint_inr, snd_comp_inr]
theorem norm_fst_le (v : P ⊕ₕ L) : ‖fst v‖ ≤ ‖v‖ := by
  rw [← abs_norm, ← abs_norm v, ← sq_le_sq, norm_sq_eq]
  exact le_add_of_nonneg_right (sq_nonneg _)
theorem norm_snd_le (v : P ⊕ₕ L) : ‖snd v‖ ≤ ‖v‖ := by
  rw [← abs_norm, ← abs_norm v, ← sq_le_sq, norm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)
theorem opNorm_fst_le : ‖(fst : P ⊕ₕ L →L[ℂ] P)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by rw [one_mul]; exact norm_fst_le v)
theorem opNorm_snd_le : ‖(snd : P ⊕ₕ L →L[ℂ] L)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by rw [one_mul]; exact norm_snd_le v)

/-! ### Block operators -/

variable {P' : Type u'} {L' : Type v'} [HSpace P'] [HSpace L']

/-- CORE-2. The block operator `[[A, B], [C, D]] : P ⊕ₕ L → P' ⊕ₕ L'`
(mQSP system matrix, public coordinate first). -/
noncomputable def block (A : P →L[ℂ] P') (B : L →L[ℂ] P') (C : P →L[ℂ] L') (D : L →L[ℂ] L') :
    P ⊕ₕ L →L[ℂ] P' ⊕ₕ L' :=
  inl ∘L A ∘L fst + inl ∘L B ∘L snd + inr ∘L C ∘L fst + inr ∘L D ∘L snd

variable (A : P →L[ℂ] P') (B : L →L[ℂ] P') (C : P →L[ℂ] L') (D : L →L[ℂ] L')

theorem block_apply (v : P ⊕ₕ L) :
    block A B C D v = mk (A (fst v) + B (snd v)) (C (fst v) + D (snd v)) := by
  ext <;> simp [block]

@[simp] theorem fst_block_apply (v : P ⊕ₕ L) :
    fst (block A B C D v) = A (fst v) + B (snd v) := by rw [block_apply, fst_mk]
@[simp] theorem snd_block_apply (v : P ⊕ₕ L) :
    snd (block A B C D v) = C (fst v) + D (snd v) := by rw [block_apply, snd_mk]

@[simp] theorem fst_block_inl : fst ∘L block A B C D ∘L inl = A := by ext x; simp
@[simp] theorem fst_block_inr : fst ∘L block A B C D ∘L inr = B := by ext x; simp
@[simp] theorem snd_block_inl : snd ∘L block A B C D ∘L inl = C := by ext x; simp
@[simp] theorem snd_block_inr : snd ∘L block A B C D ∘L inr = D := by ext x; simp

/-- Every operator between direct sums is a block operator of its four corners. -/
theorem eq_block (T : P ⊕ₕ L →L[ℂ] P' ⊕ₕ L') :
    T = block (fst ∘L T ∘L inl) (fst ∘L T ∘L inr) (snd ∘L T ∘L inl) (snd ∘L T ∘L inr) := by
  ext v
  · simp only [fst_block_apply, ContinuousLinearMap.comp_apply]
    rw [← map_add, ← map_add, ← mk_eq_inl_add_inr, mk_fst_snd]
  · simp only [snd_block_apply, ContinuousLinearMap.comp_apply]
    rw [← map_add, ← map_add, ← mk_eq_inl_add_inr, mk_fst_snd]

theorem block_ext_iff {A' : P →L[ℂ] P'} {B' : L →L[ℂ] P'} {C' : P →L[ℂ] L'} {D' : L →L[ℂ] L'} :
    block A B C D = block A' B' C' D' ↔ A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← fst_block_inl A B C D, h, fst_block_inl]
    · rw [← fst_block_inr A B C D, h, fst_block_inr]
    · rw [← snd_block_inl A B C D, h, snd_block_inl]
    · rw [← snd_block_inr A B C D, h, snd_block_inr]
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

@[simp] theorem block_one_zero_zero_one : block (1 : P →L[ℂ] P) 0 0 (1 : L →L[ℂ] L) = 1 := by
  ext v <;> simp

@[simp] theorem block_zero : block (0 : P →L[ℂ] P') (0 : L →L[ℂ] P') (0 : P →L[ℂ] L')
    (0 : L →L[ℂ] L') = 0 := by
  ext v <;> simp

theorem block_add (A' : P →L[ℂ] P') (B' : L →L[ℂ] P') (C' : P →L[ℂ] L') (D' : L →L[ℂ] L') :
    block A B C D + block A' B' C' D' = block (A + A') (B + B') (C + C') (D + D') := by
  ext v <;> simp <;> abel

theorem block_smul (c : ℂ) : c • block A B C D = block (c • A) (c • B) (c • C) (c • D) := by
  ext v <;> simp [smul_add]

variable {P'' : Type*} {L'' : Type*} [HSpace P''] [HSpace L'']

theorem block_comp_block (A' : P' →L[ℂ] P'') (B' : L' →L[ℂ] P'') (C' : P' →L[ℂ] L'')
    (D' : L' →L[ℂ] L'') :
    block A' B' C' D' ∘L block A B C D =
      block (A' ∘L A + B' ∘L C) (A' ∘L B + B' ∘L D) (C' ∘L A + D' ∘L C) (C' ∘L B + D' ∘L D) := by
  ext v <;> simp [map_add] <;> abel

theorem adjoint_block : (block A B C D)† = block (A†) (C†) (B†) (D†) := by
  simp only [block, map_add, ContinuousLinearMap.adjoint_comp, adjoint_inl, adjoint_inr,
    adjoint_fst, adjoint_snd]
  simp only [ContinuousLinearMap.comp_assoc]
  abel

/-- Block-diagonal operator `A ⊕ D`. -/
noncomputable abbrev blockDiag (A : P →L[ℂ] P') (D : L →L[ℂ] L') : P ⊕ₕ L →L[ℂ] P' ⊕ₕ L' :=
  block A 0 0 D

end DSum

end MQSP
