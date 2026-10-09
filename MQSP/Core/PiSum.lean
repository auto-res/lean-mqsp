/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.DSum

/-!
# Indexed direct sums (oracle ports) (CORE-3)

The private space of an mQSP module is the direct sum `⊕ⱼ K j` of its oracle port spaces,
modelled as `PiSum K = PiLp 2 K`. This file provides the bounded injections `single j`
and projections `proj j`, the relations `proj j ∘ single j = 1`, `∑ⱼ single j ∘ proj j = 1`,
`(single j)† = proj j`, and the port-diagonal operator `diag O = ⊕ⱼ O j` (the feedback
operation `Ô(1) = ⊕ⱼ Oⱼ` of mQSP Eq. (2.2)), which is unitary when every `O j` is.
-/

namespace MQSP

universe u v

open scoped InnerProductSpace
open Finset

namespace PiSum

variable {ι : Type u} [Fintype ι] {K : ι → Type v} [∀ i, HSpace (K i)]

/-- Projection onto port `i`. -/
noncomputable def proj (i : ι) : PiSum K →L[ℂ] K i := PiLp.proj 2 K i

omit [Fintype ι] in
theorem proj_apply (i : ι) (v : PiSum K) : proj i v = v.ofLp i := rfl

omit [Fintype ι] in
@[ext] theorem ext {v w : PiSum K} (h : ∀ i, proj i v = proj i w) : v = w :=
  PiLp.ext h

theorem norm_sq_eq (v : PiSum K) : ‖v‖ ^ 2 = ∑ i, ‖proj i v‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 K v

theorem norm_proj_le (i : ι) (v : PiSum K) : ‖proj i v‖ ≤ ‖v‖ := by
  rw [← abs_norm, ← abs_norm v, ← sq_le_sq, norm_sq_eq]
  exact Finset.single_le_sum (f := fun j => ‖proj j v‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

theorem opNorm_proj_le (i : ι) : ‖(proj i : PiSum K →L[ℂ] K i)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun v => by rw [one_mul]; exact norm_proj_le i v)

variable [DecidableEq ι]

/-- Injection of port `i`. -/
noncomputable def single (i : ι) : K i →L[ℂ] PiSum K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => PiLp.single 2 i x
      map_add' := fun x y => by rw [PiLp.single_add]
      map_smul' := fun c x => by
        apply PiLp.ext; intro j
        simp only [RingHom.id_apply, PiLp.single, WithLp.ofLp_toLp, WithLp.ofLp_smul,
          Pi.smul_apply, Pi.single_smul] }

theorem single_apply (i : ι) (x : K i) : single i x = PiLp.single 2 i x := rfl

@[simp] theorem proj_single_same (i : ι) (x : K i) : proj i (single i x) = x := by
  simp [proj_apply, single_apply, PiLp.single_eq_same]

@[simp] theorem proj_single_of_ne {i j : ι} (h : j ≠ i) (x : K i) : proj j (single i x) = 0 := by
  simp [proj_apply, single_apply, PiLp.single_eq_of_ne (p := 2) h]

@[simp] theorem proj_comp_single_same (i : ι) : proj i ∘L (single i : K i →L[ℂ] PiSum K) = 1 := by
  ext x; simp

theorem proj_comp_single_of_ne {i j : ι} (h : j ≠ i) :
    proj j ∘L (single i : K i →L[ℂ] PiSum K) = 0 := by
  ext x; simp [h]

theorem sum_single_proj : ∑ i, (single i ∘L proj i : PiSum K →L[ℂ] PiSum K) = 1 := by
  ext v j
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    one_apply_eq_self]
  rw [Finset.sum_eq_single j]
  · rw [proj_single_same]
  · intro i _ hij; rw [proj_single_of_ne (Ne.symm hij)]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem inner_single_left (i : ι) (x : K i) (v : PiSum K) :
    ⟪single i x, v⟫_ℂ = ⟪x, proj i v⟫_ℂ := by
  rw [single_apply, PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp [proj_apply, PiLp.single_eq_same]
  · intro j _ hj; simp [PiLp.single_eq_of_ne (p := 2) hj]
  · intro h; exact absurd (Finset.mem_univ i) h

@[simp] theorem adjoint_single (i : ι) : (single i : K i →L[ℂ] PiSum K)† = proj i := by
  symm; rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v x
  rw [← inner_conj_symm v (single i x), inner_single_left, inner_conj_symm]

@[simp] theorem adjoint_proj (i : ι) : (proj i : PiSum K →L[ℂ] K i)† = single i := by
  rw [← adjoint_single, ContinuousLinearMap.adjoint_adjoint]

theorem isIsometry_single (i : ι) : IsIsometry (single i : K i →L[ℂ] PiSum K) := by
  rw [IsIsometry, adjoint_single, proj_comp_single_same]

/-- The port-diagonal operator `⊕ⱼ O j` (mQSP `Ô(1) = ⊕ⱼ Oⱼ`, Eq. (2.2)). -/
noncomputable def diag (O : ∀ i, K i →L[ℂ] K i) : PiSum K →L[ℂ] PiSum K :=
  ∑ i, single i ∘L O i ∘L proj i

theorem proj_diag_apply (O : ∀ i, K i →L[ℂ] K i) (j : ι) (v : PiSum K) :
    proj j (diag O v) = O j (proj j v) := by
  simp only [diag, _root_.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single j]
  · rw [proj_single_same]
  · intro i _ hij; rw [proj_single_of_ne (Ne.symm hij)]
  · intro h; exact absurd (Finset.mem_univ j) h

@[simp] theorem proj_comp_diag (O : ∀ i, K i →L[ℂ] K i) (j : ι) :
    proj j ∘L diag O = O j ∘L proj j := by
  ext v; simp [proj_diag_apply]

@[simp] theorem diag_comp_single (O : ∀ i, K i →L[ℂ] K i) (j : ι) :
    diag O ∘L single j = single j ∘L O j := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, proj_diag_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [proj_single_of_ne h]

theorem diag_comp_diag (O O' : ∀ i, K i →L[ℂ] K i) :
    diag O ∘L diag O' = diag (fun i => O i ∘L O' i) := by
  ext v i; simp [proj_diag_apply]

theorem adjoint_diag (O : ∀ i, K i →L[ℂ] K i) : (diag O)† = diag (fun i => (O i)†) := by
  simp only [diag, map_sum, ContinuousLinearMap.adjoint_comp, adjoint_single, adjoint_proj,
    ContinuousLinearMap.comp_assoc]

@[simp] theorem diag_one : diag (fun i => (1 : K i →L[ℂ] K i)) = 1 := by
  ext v i; simp [proj_diag_apply]

theorem isUnitary_diag {O : ∀ i, K i →L[ℂ] K i} (h : ∀ i, IsUnitary (O i)) :
    IsUnitary (diag O) := by
  constructor
  · rw [adjoint_diag, diag_comp_diag]
    simp only [(h _).1]
    exact diag_one
  · rw [adjoint_diag, diag_comp_diag]
    simp only [(h _).2]
    exact diag_one

end PiSum

end MQSP
