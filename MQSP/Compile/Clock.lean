/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.BlockEncoding

/-!
# Clock states and kernel extraction (COMP-C2; mQSP §2.3, Thm 2.3, Lemma 2.4)

Quditization selects a linear combination of the public blocks of a lift by input and output
*clock states*. With a label register `Fin R` and clock register `Fin N`, a clock state is a
coefficient array `c : Fin R → Fin N → ℂ`; it defines the isometry
`clockIn c : P → Reg R (Reg N P ⊕ₕ Mm)`, `ψ ↦ ∑_{ℓ,i} c ℓ i • |ℓ⟩|i⟩ψ` (when `∑ |c ℓ i|² = 1`).
For a unitary `W` on `Reg N P ⊕ₕ Mm` (a lift, acting trivially on the label), the selected block
is the *kernel extraction* (mQSP Eq. (2.31)–(2.33), (2.36))

  `(clockIn cout)† (1_R ⊗ W) (clockIn cin) = ∑_{o,i} X o i • W_{oi}`,
  `X o i = ∑_ℓ conj (cout ℓ o) * cin ℓ i`,

where `W_{oi} = ⟨o| fst W inl |i⟩` are the public blocks. For a Toeplitz public block
`W_{oi} = G (o - i)` this is `∑ₙ cₙ(X) • G n` with the clock weights `cₙ(X) = ∑_{o-i=n} X o i`
(Eq. (2.32)). Lemma 2.4: `‖∑ X o i • E o i‖ ≤ ‖X‖_* ‖E‖`, stated here for factorised `X`.
-/

namespace MQSP

universe u v

open scoped InnerProductSpace
open Finset

namespace Clock

variable {P : Type u} {Mm : Type v} [HSpace P] [HSpace Mm] {N R : ℕ}

/-- The public block `(o, i)` of an operator on `Reg N P ⊕ₕ Mm`. -/
noncomputable def kernel (W : Reg N P ⊕ₕ Mm →L[ℂ] Reg N P ⊕ₕ Mm) (o i : Fin N) : P →L[ℂ] P :=
  Reg.proj o ∘L DSum.fst ∘L W ∘L DSum.inl ∘L Reg.single i

/-- Kernel extraction `L_X(E) = ∑_{o,i} X o i • E o i` (mQSP Eq. (2.36)). -/
noncomputable def extract (X : Fin N → Fin N → ℂ) (E : Fin N → Fin N → (P →L[ℂ] P)) :
    P →L[ℂ] P :=
  ∑ o, ∑ i, X o i • E o i

/-- The clock matrix of a pair of clock states (mQSP Eq. (1.9), (2.32)):
`X o i = ∑_ℓ conj (cout ℓ o) * cin ℓ i`. -/
def clockX (cin cout : Fin R → Fin N → ℂ) (o i : Fin N) : ℂ :=
  ∑ ℓ, (starRingEnd ℂ) (cout ℓ o) * cin ℓ i

/-- The clock weights `cₙ(X) = ∑_{o - i = n} X o i` (mQSP Eq. (2.32)). -/
def weights (X : Fin N → Fin N → ℂ) (n : ℕ) : ℂ :=
  ∑ o : Fin N, ∑ i : Fin N, if (i : ℕ) + n = (o : ℕ) then X o i else 0

/-- The clock isometry `ψ ↦ ∑_{ℓ,i} c ℓ i • |ℓ⟩ |i⟩ ψ` into the public part of the lift space. -/
noncomputable def clockIn (c : Fin R → Fin N → ℂ) : P →L[ℂ] Reg R (Reg N P ⊕ₕ Mm) :=
  ∑ ℓ, ∑ i, c ℓ i • (Reg.single ℓ ∘L DSum.inl ∘L Reg.single i)

/-- A clock state is normalised: `∑ |c ℓ i|² = 1`. -/
def IsNormalized (c : Fin R → Fin N → ℂ) : Prop := ∑ ℓ, ∑ i, ‖c ℓ i‖ ^ 2 = 1

/-! ### Auxiliary: the clock vector `|b⟩ ⊗ ·` -/

/-- The map `ψ ↦ ∑ i, b i • |i⟩ ψ` (`|b⟩ ⊗ ·`) for a clock vector `b : Fin N → ℂ`. -/
noncomputable def ket (b : Fin N → ℂ) : P →L[ℂ] Reg N P :=
  ∑ i, b i • Reg.single i

theorem proj_ket_apply (b : Fin N → ℂ) (i : Fin N) (ψ : P) :
    Reg.proj i (ket b ψ) = b i • ψ := by
  simp only [ket, _root_.sum_apply, smul_apply, map_sum, map_smul]
  rw [Finset.sum_eq_single i]
  · rw [Reg.proj_single_same]
  · intro j _ hj; rw [Reg.proj_single_of_ne (Ne.symm hj), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem norm_ket_apply_sq (b : Fin N → ℂ) (ψ : P) :
    ‖ket b ψ‖ ^ 2 = (∑ i, ‖b i‖ ^ 2) * ‖ψ‖ ^ 2 := by
  rw [Reg.norm_sq_eq, Finset.sum_mul]
  simp only [proj_ket_apply, norm_smul, mul_pow]

theorem norm_ket_apply (b : Fin N → ℂ) (ψ : P) :
    ‖ket b ψ‖ = Real.sqrt (∑ i, ‖b i‖ ^ 2) * ‖ψ‖ := by
  have hs : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg (ket b ψ)), norm_ket_apply_sq, Real.sqrt_mul hs,
    Real.sqrt_sq (norm_nonneg _)]

theorem opNorm_ket_le (b : Fin N → ℂ) :
    ‖(ket b : P →L[ℂ] Reg N P)‖ ≤ Real.sqrt (∑ i, ‖b i‖ ^ 2) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun ψ => (norm_ket_apply b ψ).le)

theorem adjoint_ket (b : Fin N → ℂ) :
    (ket b : P →L[ℂ] Reg N P)† = ∑ o, (starRingEnd ℂ) (b o) • Reg.proj o := by
  simp only [ket, map_sum, LinearIsometryEquiv.map_smulₛₗ, Reg.adjoint_single]

theorem clockIn_eq (c : Fin R → Fin N → ℂ) :
    clockIn (P := P) (Mm := Mm) c = ∑ ℓ, Reg.single ℓ ∘L DSum.inl ∘L ket (c ℓ) := by
  simp only [clockIn, ket, ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.comp_smul]

theorem proj_clockIn_apply (c : Fin R → Fin N → ℂ) (ℓ : Fin R) (ψ : P) :
    Reg.proj ℓ (clockIn (Mm := Mm) c ψ) = DSum.inl (ket (c ℓ) ψ) := by
  rw [clockIn_eq]
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single ℓ]
  · rw [Reg.proj_single_same]
  · intro j _ hj; rw [Reg.proj_single_of_ne (Ne.symm hj)]
  · intro h; exact absurd (Finset.mem_univ ℓ) h

theorem adjoint_clockIn (c : Fin R → Fin N → ℂ) :
    (clockIn (P := P) (Mm := Mm) c)† = ∑ ℓ, (ket (c ℓ))† ∘L DSum.fst ∘L Reg.proj ℓ := by
  rw [clockIn_eq]
  simp only [map_sum, ContinuousLinearMap.adjoint_comp, Reg.adjoint_single, DSum.adjoint_inl,
    ContinuousLinearMap.comp_assoc]

/-- The kernel extraction with a factorised clock matrix, as a sum over labels. -/
theorem extract_clockX_eq (W : Reg N P ⊕ₕ Mm →L[ℂ] Reg N P ⊕ₕ Mm)
    (cin cout : Fin R → Fin N → ℂ) :
    extract (clockX cin cout) (kernel W) =
      ∑ ℓ, (ket (cout ℓ))† ∘L DSum.fst ∘L W ∘L DSum.inl ∘L ket (cin ℓ) := by
  simp only [adjoint_ket]
  simp only [extract, clockX, kernel, ket, Finset.sum_smul,
    ContinuousLinearMap.comp_finsetSum, ContinuousLinearMap.finsetSum_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, Finset.smul_sum, smul_smul]
  simp only [Finset.sum_comm (s := (univ : Finset (Fin R)))]
  conv_rhs => rw [Finset.sum_comm]
  simp only [mul_comm]

theorem isIsometry_clockIn {c : Fin R → Fin N → ℂ} (h : IsNormalized c) :
    IsIsometry (clockIn (P := P) (Mm := Mm) c) := by
  refine isIsometry_of_norm (fun ψ => ?_)
  have h2 : ‖clockIn (P := P) (Mm := Mm) c ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [Reg.norm_sq_eq]
    simp only [proj_clockIn_apply, DSum.norm_inl, norm_ket_apply_sq, ← Finset.sum_mul]
    rw [show ∑ ℓ, ∑ i, ‖c ℓ i‖ ^ 2 = 1 from h, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- COMP-C2 (mQSP Eq. (2.31)/(2.33)). The clock-selected block of `1_R ⊗ W` is the kernel
extraction with the clock matrix. -/
theorem clockOut_map_clockIn (W : Reg N P ⊕ₕ Mm →L[ℂ] Reg N P ⊕ₕ Mm)
    (cin cout : Fin R → Fin N → ℂ) :
    (clockIn (Mm := Mm) cout)† ∘L Reg.map W ∘L clockIn cin =
      extract (clockX cin cout) (kernel W) := by
  rw [extract_clockX_eq, adjoint_clockIn, clockIn_eq]
  simp only [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.comp_assoc]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_eq_single ℓ]
  · congr 2
    ext ψ : 1
    simp
  · intro ℓ' _ hℓ'
    have : Reg.proj ℓ' ∘L Reg.map W ∘L Reg.single ℓ ∘L DSum.inl ∘L ket (cin ℓ) = 0 := by
      ext ψ : 1
      simp [Reg.proj_single_of_ne hℓ']
    rw [this, ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]
  · intro h; exact absurd (Finset.mem_univ ℓ) h

/-- COMP-C2 (mQSP Eq. (2.32)). For a lower-triangular Toeplitz kernel the extraction is the
weighted sum `∑_{n < N} cₙ(X) • G n`. -/
theorem extract_toeplitz (X : Fin N → Fin N → ℂ) (G : ℕ → (P →L[ℂ] P)) :
    extract X (fun o i => if (i : ℕ) ≤ o then G (o - i) else 0) =
      ∑ n ∈ Finset.range N, weights X n • G n := by
  simp only [extract, weights, Finset.sum_smul, ite_smul, zero_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ho := o.isLt
  by_cases h : (i : ℕ) ≤ o
  · rw [ite_eq_left h, Finset.sum_eq_single ((o : ℕ) - i)]
    · rw [ite_eq_left (by omega)]
    · intro n _ hn; rw [ite_eq_right (by omega)]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  · rw [ite_eq_right h, smul_zero]
    exact (Finset.sum_eq_zero fun n _ => ite_eq_right (by omega)).symm

/-- COMP-C2 (mQSP Lemma 2.4, factorised form). For `X o i = ∑_ℓ conj (a ℓ o) * b ℓ i`,
`‖L_X(kernel W)‖ ≤ (∑_ℓ ‖a ℓ‖ ‖b ℓ‖) ‖W‖`, where `‖a ℓ‖² = ∑ₒ |a ℓ o|²`. -/
theorem norm_extract_le (W : Reg N P ⊕ₕ Mm →L[ℂ] Reg N P ⊕ₕ Mm)
    (a b : Fin R → Fin N → ℂ) :
    ‖extract (clockX b a) (kernel W)‖ ≤
      (∑ ℓ, Real.sqrt (∑ o, ‖a ℓ o‖ ^ 2) * Real.sqrt (∑ i, ‖b ℓ i‖ ^ 2)) * ‖W‖ := by
  rw [extract_clockX_eq, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
  have ha : ‖(ket (a ℓ) : P →L[ℂ] Reg N P)†‖ ≤ Real.sqrt (∑ o, ‖a ℓ o‖ ^ 2) := by
    rw [LinearIsometryEquiv.norm_map]; exact opNorm_ket_le _
  have hb := opNorm_ket_le (P := P) (b ℓ)
  have hf := DSum.opNorm_fst_le (P := Reg N P) (L := Mm)
  have hi := (DSum.isIsometry_inl (P := Reg N P) (L := Mm)).opNorm_le_one
  calc _ ≤ ‖(ket (a ℓ) : P →L[ℂ] Reg N P)†‖ * (‖(DSum.fst : Reg N P ⊕ₕ Mm →L[ℂ] Reg N P)‖ *
        (‖W‖ * (‖(DSum.inl : Reg N P →L[ℂ] Reg N P ⊕ₕ Mm)‖ *
          ‖(ket (b ℓ) : P →L[ℂ] Reg N P)‖))) := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.sqrt (∑ o, ‖a ℓ o‖ ^ 2) * (1 * (‖W‖ * (1 * Real.sqrt (∑ i, ‖b ℓ i‖ ^ 2)))) := by
        gcongr
    _ = _ := by ring

/-- COMP-C2. Quditization: for normalised clock states, `1_R ⊗ W` is an encoding of the
extracted block. -/
theorem isEncodingOf_quditize {W : Reg N P ⊕ₕ Mm →L[ℂ] Reg N P ⊕ₕ Mm} (hW : IsUnitary W)
    {cin cout : Fin R → Fin N → ℂ} (hin : IsNormalized cin) (hout : IsNormalized cout) :
    IsEncodingOf (Reg.map W) (clockIn cin) (clockIn cout)
      (extract (clockX cin cout) (kernel W)) :=
  ⟨Reg.isUnitary_map hW, isIsometry_clockIn hin, isIsometry_clockIn hout,
    clockOut_map_clockIn W cin cout⟩

end Clock

end MQSP
