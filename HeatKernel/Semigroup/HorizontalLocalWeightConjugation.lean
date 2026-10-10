-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalExponentialProducts
public import HeatKernel.Semigroup.HorizontalHeatConjugation

/-! # Heat conjugation by bounded local horizontal energy weights -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace RothschildStein
open scoped BigOperators
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem norm_horizontalHeat_exponential_conjugation_le
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ψ : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hψ : MemLocalEnergy ⊤ X ψ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] ψ (g i))
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B) (a : ℝ)
    (hg : ∀ᵐ x ∂volume, ∑ i, g i x ^ 2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
      ψ hψ.1 B hB a).comp
        ((horizontalHeatOperator ⊤ X t.toNNReal).comp
          (Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
            ψ hψ.1 B hB (-a)))‖ ≤ Real.exp (a ^ 2 * t) := by
  have hgi : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ (1 : ℝ) := by
    intro i
    filter_upwards [hg] with x hx
    have hi : g i x ^ 2 ≤ ∑ j : Fin q, g j x ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (g j x)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith only [hi, hx]
  apply norm_horizontalHeat_exponential_conjugation_le_of_form_products X hX
    ψ hψ.1 B a hB (fun x i => g i x) ?_ ?_ ht
  · simpa only [Measure.restrict_univ] using hg
  · intro u
    exact exists_horizontalExponentialFormProduct X hX ψ g hψ hw B hB zero_le_one hgi (2 * a) u

end HeatKernel
