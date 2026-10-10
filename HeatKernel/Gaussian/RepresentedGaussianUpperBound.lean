-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.RepresentedEndpoint
public import HeatKernel.Gaussian.CarnotSliceIntegrability
public import HeatKernel.Gaussian.CarnotUpperBound
import Mathlib.Tactic

/-! # Gaussian upper bounds from represented endpoint evolutions

The two endpoint estimates give Gaussian decay on Carnot groups. Joint
continuity and L² representation supply every integrability condition, while
the conjugation and mean-value estimates remain explicit analytic inputs.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric RothschildStein
namespace HeatKernel.Gaussian

/-- Represented normalized evolutions with exponential conjugation bounds and
two endpoint mean-value inequalities give the Carnot Gaussian upper estimate. -/
theorem carnot_gaussian_upper_bound_of_represented_endpoint_evolutions {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → CarnotPoint G hq hqpos hspan → CarnotPoint G hq hqpos hspan → ℝ)
    (hp : ∀ y, ContinuousOn (fun w : ℝ × CarnotPoint G hq hqpos hspan ↦ p w.1 y w.2)
      (Ioi 0 ×ˢ univ))
    (T : ℝ → Lp ℝ 2 (CarnotPoint.volume G hq hqpos hspan) →L[ℝ]
      Lp ℝ 2 (CarnotPoint.volume G hq hqpos hspan))
    {t : ℝ} (ht : 0 < t) (x y : CarnotPoint G hq hqpos hspan) (C : ℝ) :
    let μ := CarnotPoint.volume G hq hqpos hspan;
    let r := Real.sqrt t / 4;
    let β := dist x y / (6 * t);
    (∀ σ > 0, ‖(distanceExponentialMultiplication μ x y β).comp
      ((T σ).comp (distanceExponentialMultiplication μ x y (-β)))‖ ≤ Real.exp (β ^ 2 * σ)) →
    (∀ s ∈ Icc (t / 2) (2 * t),
      let A := ∫ z in ball x (2 * r), p s y z ^ 2 ∂μ;
      0 < A →
      ∃ u : Lp ℝ 2 μ,
        u =ᵐ[μ] (ball x (2 * r)).indicator (fun z ↦ p s y z / Real.sqrt A) ∧
      ∃ v : ℝ × CarnotPoint G hq hqpos hspan → ℝ,
        ContinuousOn v (Ioi 0 ×ˢ univ) ∧
        (∀ σ > 0, (fun z ↦ v (σ, z)) =ᵐ[μ] T σ u) ∧
        A ≤ C ^ 2 / (r ^ 2 * μ.real (ball y (2 * r))) *
          ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
            ∫ z in ball y (2 * r), v (σ, z) ^ 2 ∂μ) →
    (p t x y ^ 2 ≤ C ^ 2 / (r ^ 2 * μ.real (ball x (2 * r))) *
      ∫ σ in Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2),
        ∫ z in ball x (2 * r), p σ y z ^ 2 ∂μ) →
    p t x y ≤ (4 * (2 : ℝ) ^ G.homogeneousDimension * Real.exp (1 / 6) * C ^ 2 /
      μ.real (ball x (Real.sqrt t))) * Real.exp (-(1 / 24 : ℝ) * (dist x y ^ 2 / t)) := by
  intro μ r β hconj hfirst hsecond
  have := CarnotPoint.properSpace G hq hqpos hspan hw
  have hβ : 0 ≤ β := div_nonneg dist_nonneg (by positivity)
  have hV : 0 < μ.real (ball y (2 * r)) := by
    dsimp [μ]
    rw [CarnotPoint.volumeReal_ball G hq hqpos hspan hw y (by dsimp [r]; positivity)]
    exact mul_pos (horizontal_unit_ball_volume_real_pos G hq hqpos hspan hw)
      (pow_pos (by dsimp [r]; positivity) _)
  have htime := integrableOn_carnot_endpoint_integral_ball_sq G hq hqpos hspan hw x
    (fun w ↦ p w.1 y w.2) (hp y) ht
    (show t ∈ Icc (t / 2) (2 * t) by constructor <;> linarith)
  apply carnot_gaussian_upper_bound_of_endpoint_mean_values G hq hqpos hspan hw ht x y
    (p t x y) C (fun σ ↦ ∫ z in ball x (2 * r), p σ y z ^ 2 ∂μ) htime ?_ hsecond
  intro s hs
  have hs' := endpoint_cylinder_subset_row_times ht hs
  let A := ∫ z in ball x (2 * r), p s y z ^ 2 ∂μ
  by_cases hpos : 0 < A
  · have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < t / 2) hs'.1
    have hc : Continuous (p s y) := (hp y).comp_continuous
      (continuous_const.prodMk continuous_id) (fun z ↦ ⟨hspos, mem_univ z⟩)
    have hf : AEStronglyMeasurable (p s y) μ := hc.aestronglyMeasurable
    obtain ⟨u, hu, v, hv, hrepr, hmean⟩ := hfirst s hs' hpos
    have heq : u = (memLp_normalized_indicator μ measurableSet_ball (p s y) hf hpos).toLp
        ((ball x (2 * r)).indicator (fun z ↦ p s y z / Real.sqrt A)) := by
      apply Lp.ext
      exact hu.trans (memLp_normalized_indicator μ measurableSet_ball (p s y) hf hpos).coeFn_toLp.symm
    rw [heq] at hrepr
    exact integral_row_sq_le_of_represented_normalized_evolution μ x y (p s y) hf T v hv
      ht hs' hβ hV hpos
      (carnot_volume_ball_ne_top G hq hqpos hspan hw y (by positivity))
      hrepr hconj hmean
  · have hzero : A = 0 := le_antisymm (le_of_not_gt hpos)
      (integral_nonneg (fun z ↦ sq_nonneg _))
    change A ≤ _
    rw [hzero]
    positivity

end HeatKernel.Gaussian
