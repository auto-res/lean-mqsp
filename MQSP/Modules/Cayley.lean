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

/-- LIB-1 (mQSP Eq. (5.35)). The Cayley junction: public `E`, private `Reg 2 E`,
`S = [[0, -i ⟨0|ₐ], [|0⟩ₐ, i (1 - Π)]]`. -/
noncomputable def cayley : Junction E (Reg 2 E) (onePort (Reg 2 E)) where
  S := DSum.block 0 ((-Complex.I) • Reg.proj 0) (Reg.single 0)
    (Complex.I • (1 - sigProj E))
  isUnitary_S := by
    sorry
  ports := Ports.one (Reg 2 E)
  delay _ := 1
  one_le_delay _ := le_rfl

variable {E}

@[simp] theorem cayley_A : (cayley E).A = 0 := by sorry
@[simp] theorem cayley_B : (cayley E).B = (-Complex.I) • Reg.proj 0 := by sorry
@[simp] theorem cayley_C : (cayley E).C = Reg.single 0 := by sorry
@[simp] theorem cayley_D : (cayley E).D = Complex.I • (1 - sigProj E) := by sorry

theorem cayley_Q (O : Reg 2 E →L[ℂ] Reg 2 E) : (cayley E).Q (oneOracle O) = O := by sorry

/-- The encoded operator `A = ⟨0|ₐ O |0⟩ₐ` of a block encoding on `Reg 2 E`. -/
noncomputable abbrev encoded (O : Reg 2 E →L[ℂ] Reg 2 E) : E →L[ℂ] E :=
  Reg.proj 0 ∘L O ∘L Reg.single 0

/-- A self-inverse (reflection) block encoding: `O† = O`, `O O = 1`. -/
structure IsSelfInverse (O : Reg 2 E →L[ℂ] Reg 2 E) : Prop where
  adjoint_eq : O† = O
  mul_self : O ∘L O = 1

/-- LIB-1 (mQSP Eq. (1.25)). The steady state of the Cayley loop is regular for every
self-inverse block encoding, and `1 + i A` is invertible on the public space. -/
theorem cayley_isRegular {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    (cayley E).IsRegular (oneOracle O) := by
  sorry

theorem isUnit_one_add_I_smul_encoded {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    IsUnit (1 + Complex.I • encoded O) := by
  sorry

/-- LIB-1 (mQSP Eq. (1.31)). The steady value of the Cayley module is the Cayley transform
`(1 - i A)(1 + i A)⁻¹` of the encoded Hermitian contraction `A = ⟨0|ₐ O |0⟩ₐ`. -/
theorem cayley_steady {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) :
    (cayley E).steady (oneOracle O) =
      (1 - Complex.I • encoded O) ∘L Ring.inverse (1 + Complex.I • encoded O) := by
  sorry

/-- LIB-1 (mQSP Eq. (1.27)). On a unit eigenvector `ψ` of `A` with real eigenvalue `x`, the
catalyst weight of the Cayley module is `2/(1 + x²)`. -/
theorem cayley_weight_eigen {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : IsSelfInverse O) {ψ : E}
    (hψ : ‖ψ‖ = 1) {x : ℝ} (hx : encoded O ψ = (x : ℂ) • ψ) :
    (cayley E).weight (oneOracle O) () ψ = 2 / (1 + x ^ 2) := by
  sorry

end Junction

end MQSP
