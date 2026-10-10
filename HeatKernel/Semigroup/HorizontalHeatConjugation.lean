-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalWeightedEnergy
public import HeatKernel.Gaussian.ConjugatedEnergy

/-! # Exponential conjugation of the horizontal heat operators

The positive-time form equation and strong continuity at zero give the conjugation bound
when exponential multiplication preserves the form domain with the prescribed gradient.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem norm_horizontalHeat_exponential_conjugation_le_of_form_products
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ψ : (Fin N → ℝ) → ℝ)
    (hψ : AEStronglyMeasurable ψ (volume.restrict (univ : Set (Fin N → ℝ))))
    (B a : ℝ) (hB : ∀ x, |ψ x| ≤ B)
    (h : (Fin N → ℝ) → Fin q → ℝ)
    (hh : ∀ᵐ x ∂volume.restrict (univ : Set (Fin N → ℝ)), ∑ i, h x i ^ 2 ≤ 1)
    (hproduct : ∀ u : energyGraph ⊤ X, ∃ w : energyGraph ⊤ X,
      energyInclusion ⊤ X w =
        Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
          ψ hψ B hB (2 * a) (energyInclusion ⊤ X u) ∧
      ∀ i, (w : GradientSpace ⊤ q).snd i
        =ᵐ[volume.restrict (univ : Set (Fin N → ℝ))] fun x ↦
          Real.exp (2 * a * ψ x) *
            ((u : GradientSpace ⊤ q).snd i x +
              2 * a * energyInclusion ⊤ X u x * h x i))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
      ψ hψ B hB a).comp
        ((horizontalHeatOperator ⊤ X t.toNNReal).comp
          (Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
            ψ hψ B hB (-a)))‖ ≤ Real.exp (a ^ 2 * t) := by
  apply Gaussian.norm_exponential_conjugation_le_of_energy
    (volume.restrict (univ : Set (Fin N → ℝ))) ψ hψ B hB
    (fun s : ℝ => horizontalHeatOperator ⊤ X s.toNNReal)
    (fun f s => -horizontalHeatGeneratorOperator ⊤ X s f) ht
  · convert! horizontalHeatOperator_zero ⊤ X using 1
    simp only [Real.toNNReal_zero]
  · intro f
    exact ((continuous_horizontalHeatOperator_univ_apply X hX f).comp
      continuous_real_toNNReal).continuousOn
  · intro f s hs
    exact hasDerivAt_horizontalHeatOperator X hX f hs.1
  · intro f s hs
    obtain ⟨w, hwf, hwg⟩ := hproduct (horizontalHeatFormVector X f s)
    rw [energyInclusion_horizontalHeatFormVector X f hs.1] at hwf hwg
    exact horizontalHeat_weighted_energy_le_of_form_product X hX f hs.1
      ψ hψ B a hB h hh w hwf hwg

end HeatKernel
