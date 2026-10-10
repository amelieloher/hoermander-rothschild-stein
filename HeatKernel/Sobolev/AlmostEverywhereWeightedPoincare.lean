-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalWeightedPoincare
public import HeatKernel.Sobolev.WeightedMeanCongruence
import Mathlib.Tactic

/-! # Squared-tent Poincaré for almost everywhere measurable representatives -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Same-ball Poincaré gives the squared-tent inequality for almost everywhere
measurable function and energy representatives. -/
theorem lintegral_tent_sq_sub_weightedMean_le_of_ae_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : AEMeasurable f (volume G hq hqpos hspan))
    (hfi : IntegrableOn f (ball x r) (volume G hq hqpos hspan))
    (hf₂ : IntegrableOn (fun y => f y ^ 2) (ball x r) (volume G hq hqpos hspan))
    {g : CarnotPoint G hq hqpos hspan → ℝ≥0∞} (hg : AEMeasurable g (volume G hq hqpos hspan)) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, g y ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ 2) *
      ENNReal.ofReal ((f y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0 ^ 2) f) ^ 2) ∂volume G hq hqpos hspan) ≤
      (3 * (P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ 2) * g y ∂volume G hq hqpos hspan := by
  have he := hf.ae_eq_mk
  have hge := hg.ae_eq_mk
  have hfi' := hfi.congr (ae_restrict_of_ae he)
  have hf₂' : IntegrableOn (fun y => hf.mk f y ^ 2) (ball x r) (volume G hq hqpos hspan) := by
    apply hf₂.congr
    filter_upwards [ae_restrict_of_ae he] with y hy
    rw [hy]
  have hpi : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((hf.mk f y -
        (∫ z in ball x s, hf.mk f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, hg.mk g y ∂volume G hq hqpos hspan := by
    intro s hs hsr
    rw [← Sobolev.lintegral_sub_setAverage_sq_congr_ae (ball x s) (ae_restrict_of_ae he),
      ← lintegral_congr_ae (ae_restrict_of_ae hge)]
    exact hpoincare s hs hsr
  have H := lintegral_tent_sq_sub_weightedMean_le_of_poincare G hq hqpos hspan hw x hr
    hf.measurable_mk hfi' hf₂' hg.measurable_mk hpi
  rw [← Sobolev.lintegral_weighted_variance_congr_ae
    (fun y => max (1 - dist x y / r) 0 ^ 2) he] at H
  have henergy : (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ 2) * g y
      ∂volume G hq hqpos hspan) =
      ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ 2) * hg.mk g y
        ∂volume G hq hqpos hspan := by
    apply lintegral_congr_ae
    filter_upwards [hge] with y hy
    rw [hy]
  rwa [← henergy] at H

end HeatKernel.CarnotPoint
