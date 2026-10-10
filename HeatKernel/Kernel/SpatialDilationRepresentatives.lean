-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SpatialFormPullbacks

/-! # Scalar representatives of spatial normalized dilation -/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- Spatial normalized dilation represents the normalized group pullback almost everywhere. -/
theorem spatialNormalizedDilation_ae {N : ℕ} (G : HomogeneousGroup N) {r : ℝ} (hr : 0 < r)
    (f : SpatialL2 (N := N) ⊤) :
    spatialNormalizedDilation G hr f =ᵐ[volume]
      fun x => Real.sqrt (r ^ G.homogeneousDimension) * f (G.dilate r x) := by
  let P := scaledMeasurePullback (G2.dilationHomeomorph G r hr).continuous.measurable
    (J := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹))
    (map_dilate_restrict_univ_volume G hr) ENNReal.ofReal_ne_top
  have hp := scaledMeasurePullback_ae (G2.dilationHomeomorph G r hr).continuous.measurable
    (μ := volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))
    (J := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹))
    (map_dilate_restrict_univ_volume G hr) ENNReal.ofReal_ne_top f
  change P f =ᵐ[volume.restrict Set.univ] f ∘ G.dilate r at hp
  have hp' : P f =ᵐ[volume] f ∘ G.dilate r := by
    simpa only [Measure.restrict_univ] using hp
  have hs0 := Lp.coeFn_smul (Real.sqrt (r ^ G.homogeneousDimension)) (P f)
  change (Real.sqrt (r ^ G.homogeneousDimension) • P f : SpatialL2 (N := N) ⊤) =ᵐ[volume.restrict Set.univ]
    (fun x => Real.sqrt (r ^ G.homogeneousDimension) * P f x) at hs0
  have hs : (Real.sqrt (r ^ G.homogeneousDimension) • P f : SpatialL2 (N := N) ⊤) =ᵐ[volume]
      fun x => Real.sqrt (r ^ G.homogeneousDimension) * P f x := by
    simpa only [Measure.restrict_univ] using hs0
  change (Real.sqrt (r ^ G.homogeneousDimension) • P f : SpatialL2 (N := N) ⊤) =ᵐ[volume] _
  filter_upwards [hs, hp'] with x hx hy
  rw [hx]
  exact congrArg (fun z : ℝ => Real.sqrt (r ^ G.homogeneousDimension) * z) hy

end HeatKernel
