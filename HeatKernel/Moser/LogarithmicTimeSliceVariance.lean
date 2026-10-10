-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicUniformVariance
public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Bridge.ParabolicLocalEnergy
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Uniform logarithmic variance on almost every time slice -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric TopologicalSpace RothschildStein
namespace HeatKernel

/-- The logarithmic variance estimate holds on almost every time slice, using
the specified weak gradient and any representative of the weighted mean. -/
theorem exists_uniform_logarithmic_time_slice_variance {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (x : CarnotPoint G hq hqpos hspan) (ρ R : ℝ), 0 < ρ → ρ < R →
    ∀ (I : Opens ℝ) (J : Set ℝ), J ⊆ (I : Set ℝ) →
    ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
      (m : ℝ → ℝ) (ell upper ε : ℝ), 0 < ell → 0 < ε →
    let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x R,
      isOpen_horizontalBall G hq hqpos hspan x R⟩
    let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / ρ) 0
    IsLocalWeakSolution G hq hqpos hw hspan coeff I U u →
    WeakSolutionEnergyInterface (G.horizontalFields hq) coeff I U u g →
    (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
    (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
    (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict
      ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ u z.1 z.2) →
    (m =ᵐ[volume.restrict J] (fun s => (∫ y, η y^2)⁻¹ *
      ∫ y, η y^2 * (Real.log (u s y + ε) - Real.log ε))) →
    ∀ᵐ s ∂volume.restrict J,
      Integrable (fun y : CarnotPoint G hq hqpos hspan =>
        η y^2 * (Real.log (u s y + ε) - Real.log ε - m s)^2)
        (CarnotPoint.volume G hq hqpos hspan) ∧
      (∫ y : CarnotPoint G hq hqpos hspan,
        η y^2 * (Real.log (u s y + ε) - Real.log ε - m s)^2
          ∂CarnotPoint.volume G hq hqpos hspan) ≤
        (K * ρ^2 / ell) * ∫ y : CarnotPoint G hq hqpos hspan, ∑ i, ∑ j, coeff s y i j *
          (η y * ((u s y + ε)⁻¹ * g j s y)) *
          (η y * ((u s y + ε)⁻¹ * g i s y)) ∂CarnotPoint.volume G hq hqpos hspan := by
  obtain ⟨K, hK, hspatial⟩ := exists_uniform_logarithmic_matrix_tent_variance G hq hqpos hspan hw
  refine ⟨K, hK, ?_⟩
  intro x ρ R hρ hρR I J hJ coeff u g m ell upper ε hell hε U η hu hg ha hquad hn hmean
  obtain ⟨_, _, hlocal⟩ := hu.exists_local_energy_slices G hq hqpos hw hspan coeff I U
  have hslice (i : Fin q) : ∀ᵐ s ∂volume.restrict (I : Set ℝ),
      AEStronglyMeasurable (fun y : CarnotPoint G hq hqpos hspan => g i s y)
        ((CarnotPoint.volume G hq hqpos hspan).restrict (ball x R)) := by
    have H := hg.local_bounds.aestronglyMeasurable_gradient i
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at H
    rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
    change ∀ᵐ s ∂volume.restrict (I : Set ℝ),
      AEStronglyMeasurable (g i s) (volume.restrict (U : Set (Fin N → ℝ)))
    exact H.prodMk_left
  have hnprod : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂(volume.restrict (I : Set ℝ)).prod (volume.restrict (U : Set (Fin N → ℝ))),
        0 ≤ u z.1 z.2 := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hn
  have hco := Measure.ae_ae_of_ae_prod hquad
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hJ hlocal,
    ae_restrict_of_ae_restrict_of_subset hJ hg.weak_gradient,
    ae_restrict_of_ae_restrict_of_subset hJ (Measure.ae_ae_of_ae_prod hnprod),
    ae_restrict_of_ae_restrict_of_subset hJ (ae_all_iff.mpr hslice),
    ae_restrict_of_ae hco, hmean] with s hs hgrad hn' hgm hqs hm
  have hqs' : ∀ᵐ y ∂volume, ∀ ξ : Fin q → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (coeff s y) ξ ∧
      matrixEnergy (coeff s y) ξ ≤ upper * coordinateNormSq ξ := by
    filter_upwards [hqs] with y hy ξ
    simpa only [coordinateNormSq, matrixEnergy, mul_assoc, mul_left_comm, mul_comm] using hy.2 ξ
  obtain ⟨hi, hv⟩ := hspatial x ρ R hρ hρR (u s) (fun i y => g i s y) hs.1 hgrad hn' hgm
    (fun i j y => coeff s y i j) ell upper ε hell hε
    (fun i j => (ha i j).comp (measurable_const.prodMk measurable_id)) hqs'
  have hη (y : CarnotPoint G hq hqpos hspan) :
      η y = max (1 - dist x y / ρ) 0 := by rw [dist_edist, CarnotPoint.edist_eq]
  have hm' : m s = (∫ y : CarnotPoint G hq hqpos hspan,
      η y^2 * (Real.log (u s y + ε) - Real.log ε) ∂CarnotPoint.volume G hq hqpos hspan) /
      (∫ y : CarnotPoint G hq hqpos hspan, η y^2 ∂CarnotPoint.volume G hq hqpos hspan) := by
    change m s = (∫ y : Fin N → ℝ, η y^2 * (Real.log (u s y + ε) - Real.log ε)) /
      (∫ y : Fin N → ℝ, η y^2)
    simpa only [div_eq_mul_inv, mul_comm] using hm
  exact ⟨by simpa only [← hη, ← hm'] using hi,
    by simpa only [← hη, ← hm'] using hv⟩

end HeatKernel
