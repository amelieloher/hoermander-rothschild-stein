-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyPullbackRepresentatives
public import HeatKernel.Form.ScaledEnergyPullbacks
import Mathlib.Tactic.Linter

/-! # Bounded energy operators induced by smooth measure-scaling homeomorphisms -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal

namespace HeatKernel

variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (T : (Fin N → ℝ) ≃ₜ (Fin N → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    {J : ℝ≥0∞} (hJ : J ≠ ⊤) (hm : Measure.map T volume = J • volume) (c : ℝ)
    (hD : ∀ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ∀ i,
      fieldDerivative (X i) (f ∘ T) = (fun x => c * fieldDerivative (X i) f (T x)))

include hT hD in
/-- The spatial L² pullback has a canonical action on the closed energy graph. -/
theorem scaledMeasurePullback_preserves_energyGraph (u : energyGraph (N := N) ⊤ X) :
    gradientPullbackPair ⊤
      (scaledMeasurePullback T.continuous.measurable
        (by simpa only [Opens.coe_top, Measure.restrict_univ] using hm) hJ)
      c (u : GradientSpace (N := N) ⊤ q) ∈ energyGraph ⊤ X := by
  obtain ⟨z, _, hf, _, hg, _, _⟩ := exists_energyGraph_comp_scaledMeasure X T hT hJ hm c hD u u
  apply gradientPullbackPair_mem_of_representatives X T _ c ?_ u z hf hg
  intro f
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    scaledMeasurePullback_ae T.continuous.measurable
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hm) hJ f

/-- Smooth measure-scaling homeomorphisms act by bounded linear maps on the energy domain. -/
def scaledEnergyPullbackLinearMap : energyGraph (N := N) ⊤ X →L[ℝ] energyGraph (N := N) ⊤ X :=
  energyPullbackLinearMap ⊤ X
    (scaledMeasurePullback T.continuous.measurable
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hm) hJ) c
    (scaledMeasurePullback_preserves_energyGraph X T hT hJ hm c hD)

/-- The bounded energy map intertwines its inclusion with the spatial L² pullback. -/
theorem energyInclusion_scaledEnergyPullbackLinearMap (u : energyGraph (N := N) ⊤ X) :
    energyInclusion ⊤ X (scaledEnergyPullbackLinearMap X T hT hJ hm c hD u) =
      scaledMeasurePullback T.continuous.measurable
        (by simpa only [Opens.coe_top, Measure.restrict_univ] using hm) hJ (energyInclusion ⊤ X u) := rfl

/-- The bounded energy map represents composition by the original homeomorphism. -/
theorem energyInclusion_scaledEnergyPullbackLinearMap_ae (u : energyGraph (N := N) ⊤ X) :
    energyInclusion ⊤ X (scaledEnergyPullbackLinearMap X T hT hJ hm c hD u) =ᵐ[volume]
      (energyInclusion ⊤ X u) ∘ T := by
  rw [energyInclusion_scaledEnergyPullbackLinearMap]
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    scaledMeasurePullback_ae T.continuous.measurable
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hm) hJ (energyInclusion ⊤ X u)

/-- The bounded pullback operator has exact bilinear energy scaling. -/
theorem horizontalEnergy_scaledEnergyPullbackLinearMap (u v : energyGraph (N := N) ⊤ X) :
    horizontalEnergy ⊤ X (scaledEnergyPullbackLinearMap X T hT hJ hm c hD u)
      (scaledEnergyPullbackLinearMap X T hT hJ hm c hD v) =
        c ^ 2 * J.toReal * horizontalEnergy ⊤ X u v := by
  exact horizontalEnergy_energyPullbackLinearMap ⊤ X
    (scaledMeasurePullback T.continuous.measurable
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hm) hJ) c J.toReal
    (scaledMeasurePullback_preserves_energyGraph X T hT hJ hm c hD)
    (fun f g => inner_scaledMeasurePullback T.measurableEmbedding _ hJ f g) u v



end HeatKernel
