-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalPoincareLayers
public import HeatKernel.Sobolev.TentPoincare
import Mathlib.Tactic

/-! # Linear horizontal tent estimates about the half-ball average -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Same-ball Poincaré controls the linear tent-weighted oscillation about the half-ball mean. -/
theorem lintegral_tent_sub_halfBallAverage_le_of_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f)
    (hfi : IntegrableOn f (ball x r) (volume G hq hqpos hspan))
    (hf₂ : IntegrableOn (fun y => f y ^ 2) (ball x r) (volume G hq hqpos hspan))
    {g : CarnotPoint G hq hqpos hspan → ℝ≥0∞} (hg : Measurable g) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, g y ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) *
      ENNReal.ofReal ((f y - (∫ z in ball x (r / 2), f z ∂volume G hq hqpos hspan) /
        (volume G hq hqpos hspan).real (ball x (r / 2))) ^ 2) ∂volume G hq hqpos hspan) ≤
      ((P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) * g y ∂volume G hq hqpos hspan := by
  let _ : SFinite (volume G hq hqpos hspan) :=
    inferInstanceAs (SFinite (MeasureTheory.volume : Measure (Fin N → ℝ)))
  let c := (∫ z in ball x (r / 2), f z ∂volume G hq hqpos hspan) /
    (volume G hq hqpos hspan).real (ball x (r / 2))
  have hlayer (s : ℝ) : {y : CarnotPoint G hq hqpos hspan | dist x y / r < s} =
      ball x (s * r) := by
    ext y
    simp only [mem_ofPred_eq, mem_ball, dist_comm y x]
    exact div_lt_iff₀ hr
  have hsmall : ∀ s ∈ Ioo (0 : ℝ) (1 / 2),
      (∫⁻ y in {y | dist x y / r < s}, ENNReal.ofReal ((f y - c) ^ 2) ∂volume G hq hqpos hspan) ≤
        (P * ENNReal.ofReal (r / 2) ^ 2) *
          ∫⁻ y in {y | dist x y / r < 1 / 2}, g y ∂volume G hq hqpos hspan := by
    intro s hs
    rw [hlayer s, hlayer (1 / 2)]
    have he : (1 / 2 : ℝ) * r = r / 2 := by ring
    rw [he]
    exact lintegral_sub_halfBallAverage_sq_le_on_small_layer G hq hqpos hspan x hr hs.2.le
      (hpoincare (r / 2) (by positivity) (by linarith))
  have hlarge : ∀ s ∈ Ico (1 / 2 : ℝ) 1,
      (∫⁻ y in {y | dist x y / r < s}, ENNReal.ofReal ((f y - c) ^ 2) ∂volume G hq hqpos hspan) ≤
        (ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
          ∫⁻ y in {y | dist x y / r < s}, g y ∂volume G hq hqpos hspan := by
    intro s hs
    rw [hlayer s]
    have hsub : ball x (s * r) ⊆ ball x r := ball_subset_ball (by nlinarith [hs.2])
    apply lintegral_sub_halfBallAverage_sq_le_on_large_layer G hq hqpos hspan hw x hr hs.1 hs.2.le
      (hfi.mono_set hsub) (hf₂.mono_set hsub)
    exact hpoincare (s * r) (mul_pos (by linarith [hs.1]) hr) (by nlinarith [hs.2])
  have H := Sobolev.lintegral_tent_mul_le_of_layer_estimates
    (by fun_prop : Measurable (fun y : CarnotPoint G hq hqpos hspan => dist x y / r))
    (fun y => div_nonneg dist_nonneg hr.le)
    (by fun_prop : Measurable (fun y => ENNReal.ofReal ((f y - c) ^ 2))) hg hsmall hlarge
  simpa only [c] using H

end HeatKernel.CarnotPoint
