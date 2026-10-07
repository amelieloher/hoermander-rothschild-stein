-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FieldPowerBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The jet vanishing step on the actual
open coefficient domain, using the existing G3 field derivative bound. -/
theorem iteratedFDeriv_fieldDerivative_zero_on {N r k : ℕ}
    (Ω : Opens (Fin N → ℝ)) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (u : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∈ Ω)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (hz : ∀ j < r, iteratedFDeriv ℝ j u x = 0) (hk : k + 1 < r) :
    iteratedFDeriv ℝ k (fieldDerivative V u) x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  refine (G3.norm_iteratedFDeriv_fieldDerivative_le Ω V hV u hu k hx).trans_eq ?_
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [hz (i+1) (by omega),norm_zero,mul_zero,zero_mul]

/-- The leading error jet also vanishes if
the field vanishes at the base point; coefficients are only locally smooth. -/
theorem iteratedFDeriv_fieldDerivative_zero_of_field_zero_on {N k : ℕ}
    (Ω : Opens (Fin N → ℝ)) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (u : (Fin N → ℝ) → ℝ) {x : Fin N → ℝ} (hx : x ∈ Ω)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (hz : ∀ j < k + 1, iteratedFDeriv ℝ j u x = 0) (hVx : V x = 0) :
    iteratedFDeriv ℝ k (fieldDerivative V u) x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  refine (G3.norm_iteratedFDeriv_fieldDerivative_le Ω V hV u hu k hx).trans_eq ?_
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  by_cases he : i = k
  · subst i
    rw [Nat.sub_self,norm_iteratedFDeriv_zero,hVx,norm_zero,mul_zero]
  · rw [hz (i+1) (by omega),norm_zero,mul_zero,zero_mul]
end RothschildStein.L1
