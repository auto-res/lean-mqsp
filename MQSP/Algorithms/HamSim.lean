/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Compose.Substitute
import MQSP.Compose.Delay
import MQSP.Modules.Query
import MQSP.Modules.WeightedCayley
import MQSP.Resource.Cost
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Hamiltonian simulation with weighted query cost: the ideal network (ALG-1; mQSP §1.1.3, Thm 6.1)

The mQSP Hamiltonian-simulation network is `Exp_τ ∘ WeightedCayley`: the weighted Cayley
junction turns the block encodings `Vⱼ = Be[Hⱼ/λⱼ]` into the unitary Cayley transform
`W = (1 - M)(1 + M)⁻¹` of the load `M = i ∑ⱼ Hⱼ/Λ`, and the exponential transform
`Exp_τ(w) = exp(-τ (1 - w)/(1 + w))` linearises the phase, giving `exp(-τ M) = e^{-iτ ∑ Hⱼ/Λ}`;
with `τ = tΛ` this is `e^{-it ∑ Hⱼ}` (Eq. (1.43), (5.49)).

The exponential transform has no finite-dimensional *exact* realisation (its ideal system
has infinitely many private modes, Eq. (1.45)); finite realisations approximate it (Thm 5.6).
We therefore separate *specification* from *implementation*: `IsExpModule τ M` says that the
module `M` (one port) has steady value `Exp_τ(W)` on every unitary port oracle `W` with
`1 + W` invertible. The theorem `hamSim_steady` then shows that substituting the weighted
Cayley junction into the port of any such module yields a network whose steady value is
exactly `e^{-iτ ∑ Hⱼ/Λ}`; the per-oracle query schedule is set by the delays
(`withDelay`), giving `⌊(N-1)/rⱼ⌋` queries to `Hⱼ` at horizon `N` and weighted cost
`∑ⱼ Cⱼ ⌊(N-1)/rⱼ⌋` (mQSP Eq. (1.18)).
-/

namespace MQSP

universe u v w

open scoped InnerProductSpace
open Finset

namespace Junction

variable {E : Type u} [HSpace E]

/-- The exponential transform of a unitary `W` with `1 + W` invertible:
`Exp_τ(W) = exp(-τ (1 - W)(1 + W)⁻¹)` (mQSP Eq. (1.43)). -/
noncomputable def expTransform (τ : ℝ) (W : E →L[ℂ] E) : E →L[ℂ] E :=
  NormedSpace.exp ((-(τ : ℂ)) • ((1 - W) ∘L Ring.inverse (1 + W)))

/-- ALG-1 (specification). A one-port module on `E` is an *exponential-transform module* of
parameter `τ` if its steady value on every unitary port oracle `W` with `1 + W` invertible is
`Exp_τ(W)`. -/
def IsExpModule {L : Type v} [HSpace L] (τ : ℝ) (M : Junction E L (onePort E)) : Prop :=
  ∀ W : E →L[ℂ] E, IsUnitary W → IsUnit (1 + W) →
    M.IsRegular (oneOracle W) ∧ M.steady (oneOracle W) = expTransform τ W

section CayleyAlgebra

variable {M R : E →L[ℂ] E}

private theorem mul_R_eq (hR1 : (1 + M) * R = 1) : M * R = 1 - R := by
  rw [add_mul, one_mul] at hR1
  exact eq_sub_of_add_eq' hR1

private theorem one_add_cayley (hR1 : (1 + M) * R = 1) : 1 + (1 - M) * R = R + R := by
  rw [sub_mul, one_mul, mul_R_eq hR1]
  abel

private theorem cayley_isometry (hM : M† = -M) (hR1 : (1 + M) * R = 1) :
    star ((1 - M) * R) * ((1 - M) * R) = 1 := by
  have hM' : star M = -M := by rw [ContinuousLinearMap.star_eq_adjoint, hM]
  have hRd : star R * (1 - M) = 1 := by
    have h := congrArg star hR1
    rwa [star_mul, star_add, star_one, hM', ← sub_eq_add_neg] at h
  have hcomm : (1 + M) * (1 - M) = (1 - M) * (1 + M) := by noncomm_ring
  rw [star_mul, star_sub, star_one, hM', sub_neg_eq_add]
  calc star R * (1 + M) * ((1 - M) * R) = star R * ((1 + M) * (1 - M)) * R := by
        simp only [mul_assoc]
    _ = star R * (1 - M) * ((1 + M) * R) := by rw [hcomm]; simp only [mul_assoc]
    _ = 1 := by rw [hRd, hR1, one_mul]

end CayleyAlgebra

/-- The Cayley transform of a skew-adjoint load `M` (`M† = -M`) is unitary. -/
theorem isUnitary_cayleyTransform {Mload : E →L[ℂ] E} (hM : Mload† = -Mload)
    (hu : IsUnit (1 + Mload)) : IsUnitary ((1 - Mload) ∘L Ring.inverse (1 + Mload)) := by
  apply isUnitary_of_isIsometry
  have h := cayley_isometry hM (Ring.mul_inverse_cancel _ hu)
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def] at h

/-- `1 + W` is invertible for the Cayley transform `W = (1 - M)(1 + M)⁻¹` of a load with
`1 + M` invertible, and `(1 - W)(1 + W)⁻¹ = M` (the Cayley transform is an involution). -/
theorem isUnit_one_add_cayleyTransform {Mload : E →L[ℂ] E} (hu : IsUnit (1 + Mload)) :
    IsUnit (1 + (1 - Mload) ∘L Ring.inverse (1 + Mload)) := by
  have h : 1 + (1 - Mload) ∘L Ring.inverse (1 + Mload) =
      algebraMap ℂ (E →L[ℂ] E) 2 * Ring.inverse (1 + Mload) := by
    rw [← Algebra.smul_def, two_smul, ← ContinuousLinearMap.mul_def,
      one_add_cayley (Ring.mul_inverse_cancel _ hu)]
  rw [h]
  exact ((isUnit_iff_ne_zero.2 two_ne_zero).map _).mul hu.ringInverse

theorem cayleyTransform_involutive {Mload : E →L[ℂ] E} (hu : IsUnit (1 + Mload)) :
    (1 - (1 - Mload) ∘L Ring.inverse (1 + Mload)) ∘L
      Ring.inverse (1 + (1 - Mload) ∘L Ring.inverse (1 + Mload)) = Mload := by
  have hR1 := Ring.mul_inverse_cancel _ hu
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def]
  refine ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ?_).2 ?_).symm
  · rw [ContinuousLinearMap.mul_def]
    exact isUnit_one_add_cayleyTransform hu
  · rw [one_add_cayley hR1, mul_add, mul_R_eq hR1, sub_mul, one_mul, mul_R_eq hR1]
    abel

/-- `Exp_τ` of the Cayley transform of `M` is `exp(-τ M)`. -/
theorem expTransform_cayleyTransform (τ : ℝ) {Mload : E →L[ℂ] E} (hu : IsUnit (1 + Mload)) :
    expTransform τ ((1 - Mload) ∘L Ring.inverse (1 + Mload)) =
      NormedSpace.exp ((-(τ : ℂ)) • Mload) := by
  rw [expTransform, cayleyTransform_involutive hu]

variable {ι : Type w} [Fintype ι] [DecidableEq ι] {K : ι → Type u} [∀ i, HSpace (K i)]

/-- ALG-1 (mQSP Eq. (1.43)/(5.49), ideal network). Substituting the weighted Cayley junction
into the port of an exponential-transform module gives the steady value `exp(-τ M)` with
`M = i (K₀ + ∑ⱼ Cⱼ† Vⱼ Cⱼ)` the load: Hamiltonian simulation. -/
theorem hamSim_steady {L : Type v} [HSpace L] {τ : ℝ} {Mexp : Junction E L (onePort E)}
    (hexp : IsExpModule τ Mexp) (cd : CayleyData E K) {V : OracleTuple K}
    (hV : CayleyData.SelfInverse V)
    {O : OracleTuple (Sum.elim (onePort E) K)} (hid : O.left () = 1)
    (hO : O.right = CayleyData.oracles V) :
    (Mexp.subst () cd.junction).steady O =
      NormedSpace.exp ((-(τ : ℂ)) • cd.load V) := by
  have hB : cd.junction.IsRegular O.right := hO ▸ cd.isRegular hV
  have hW : substOuter () cd.junction O =
      oneOracle ((1 - cd.load V) ∘L Ring.inverse (1 + cd.load V)) := by
    funext u
    cases u
    rw [substOuter, Function.update_self, hO, cd.steady_eq hV]
    rfl
  have hu := cd.isUnit_one_add_load hV
  obtain ⟨hreg, hst⟩ := hexp _ (isUnitary_cayleyTransform (cd.load_adjoint hV) hu)
    (isUnit_one_add_cayleyTransform hu)
  rw [subst_steady Mexp () cd.junction hid hB (hW ▸ hreg), hW, hst,
    expTransform_cayleyTransform τ hu]

/-- The Hamiltonian-simulation network with per-oracle delays `r` makes `⌊(N-1)/rⱼ⌋` queries
to oracle `j` at horizon `N` (the identity wire `()` costs nothing). -/
theorem hamSim_queries {L : Type v} [HSpace L] (Mexp : Junction E L (onePort E))
    (cd : CayleyData E K) (r : Unit ⊕ ι → ℕ) (hr : ∀ j, 1 ≤ r j) (N : ℕ) (j : ι) :
    ((Mexp.subst () cd.junction).withDelay r hr).queries N (Sum.inr j) = (N - 1) / r (Sum.inr j) :=
  withDelay_queries _ r hr N (Sum.inr j)

end Junction

end MQSP
