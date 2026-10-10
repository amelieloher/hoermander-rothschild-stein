-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalHeatFormVector
public import HeatKernel.Gaussian.WeightedFormEquation

/-! # Weighted energy bounds along the horizontal heat flow

An exponential product in the form domain with its Leibniz gradient gives the weighted
energy inequality for the concrete heat generator.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem horizontalHeat_weighted_energy_le_of_form_product
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (f : SpatialL2 (N := N) ⊤) {t : ℝ} (ht : 0 < t)
    (ψ : (Fin N → ℝ) → ℝ)
    (hψ : AEStronglyMeasurable ψ (volume.restrict (univ : Set (Fin N → ℝ))))
    (B a : ℝ) (hB : ∀ x, |ψ x| ≤ B)
    (h : (Fin N → ℝ) → Fin q → ℝ)
    (hh : ∀ᵐ x ∂volume.restrict (univ : Set (Fin N → ℝ)), ∑ i, h x i ^ 2 ≤ 1)
    (w : energyGraph ⊤ X)
    (hwf : energyInclusion ⊤ X w =
      Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
        ψ hψ B hB (2 * a) (horizontalHeatOperator ⊤ X t.toNNReal f))
    (hwg : ∀ i, (w : GradientSpace ⊤ q).snd i
      =ᵐ[volume.restrict (univ : Set (Fin N → ℝ))] fun x ↦
        Real.exp (2 * a * ψ x) *
          (((horizontalHeatFormVector X f t : GradientSpace ⊤ q).snd i) x +
            2 * a * horizontalHeatOperator ⊤ X t.toNNReal f x * h x i)) :
    inner ℝ
      (Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
        ψ hψ B hB a (horizontalHeatOperator ⊤ X t.toNNReal f))
      (Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
        ψ hψ B hB a (-horizontalHeatGeneratorOperator ⊤ X t f)) ≤
      a ^ 2 * ‖Gaussian.exponentialMultiplication
        (volume.restrict (univ : Set (Fin N → ℝ))) ψ hψ B hB a
          (horizontalHeatOperator ⊤ X t.toNNReal f)‖ ^ 2 := by
  have hform : horizontalEnergy ⊤ X (horizontalHeatFormVector X f t) w =
      inner ℝ (-(-horizontalHeatGeneratorOperator ⊤ X t f)) (energyInclusion ⊤ X w) := by
    simpa only [neg_neg] using horizontalEnergy_horizontalHeatFormVector X hX f ht w
  have hwf' : energyInclusion ⊤ X w =
      Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
        ψ hψ B hB (2 * a) (energyInclusion ⊤ X (horizontalHeatFormVector X f t)) := by
    rw [energyInclusion_horizontalHeatFormVector X f ht]
    exact hwf
  have hwg' : ∀ i, (w : GradientSpace ⊤ q).snd i
      =ᵐ[volume.restrict (univ : Set (Fin N → ℝ))] fun x ↦
        Real.exp (2 * a * ψ x) *
          (((horizontalHeatFormVector X f t : GradientSpace ⊤ q).snd i) x +
            2 * a * energyInclusion ⊤ X (horizontalHeatFormVector X f t) x * h x i) := by
    rw [energyInclusion_horizontalHeatFormVector X f ht]
    exact hwg
  have he := Gaussian.inner_exponential_le_of_horizontal_form_equation ⊤ X
    (horizontalHeatFormVector X f t) w (-horizontalHeatGeneratorOperator ⊤ X t f)
    ψ hψ B hB a h hh hwf' hwg' hform
  rw [energyInclusion_horizontalHeatFormVector X f ht] at he
  exact he

end HeatKernel
