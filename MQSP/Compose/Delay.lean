/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Compile.Lift

/-!
# Changing the port delays (COMP-8; mQSP §5.2 Delay)

`Delay` replaces the feedback marker `zⱼ Oⱼ` by `zⱼ^{rⱼ} Oⱼ`: it changes the schedule but not the
steady state. At horizon `N` the compiled circuit then makes `⌊(N-1)/rⱼ⌋` calls to port `j`.
The steady value, catalyst and weights are unchanged (they do not depend on delays).
-/

namespace MQSP

universe u v w x

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-- COMP-8 (mQSP §5.2 Delay). The same junction with new port delays `r`. -/
def withDelay (r : ι → ℕ) (hr : ∀ j, 1 ≤ r j) : Junction P L K where
  S := M.S
  isUnitary_S := M.isUnitary_S
  ports := M.ports
  delay := r
  one_le_delay := hr

variable (r : ι → ℕ) (hr : ∀ j, 1 ≤ r j)

@[simp] theorem withDelay_delay (j : ι) : (M.withDelay r hr).delay j = r j := rfl

theorem withDelay_steady (O : OracleTuple K) : (M.withDelay r hr).steady O = M.steady O := rfl

theorem withDelay_catalyst (O : OracleTuple K) :
    (M.withDelay r hr).catalyst O = M.catalyst O := rfl

theorem withDelay_isRegular_iff (O : OracleTuple K) :
    (M.withDelay r hr).IsRegular O ↔ M.IsRegular O := Iff.rfl

theorem withDelay_weight (O : OracleTuple K) (j : ι) (ψ : P) :
    (M.withDelay r hr).weight O j ψ = M.weight O j ψ := rfl

/-- The compiled circuit of horizon `N` calls port `j` exactly `⌊(N-1)/rⱼ⌋` times. -/
theorem withDelay_queries (N : ℕ) (j : ι) :
    (M.withDelay r hr).queries N j = (N - 1) / r j :=
  (M.withDelay r hr).queries_eq N j

end Junction

end MQSP
