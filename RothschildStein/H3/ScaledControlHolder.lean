-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ScaledCutoffHolder
public import RothschildStein.H3.GlobalMeanValue
public import RothschildStein.H3.ControlMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Field derivative bounds imply the scaled Hölder norm in the control
metric under the global-flow and metric-identification hypotheses. -/
theorem scaled_control_holderNorm_of_controlNorm {N q : ℕ} {G : HomogeneousGroup N}
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {a M D : ℝ} {C : Fin q → ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hsup : ∀ x, |f x| ≤ M)
    (hfirst : ∀ x, ∀ i : Fin q, |fderiv ℝ f x (Y i.succ x)| ≤ C i)
    (hdrift : ∀ x, |fderiv ℝ f x (Y 0 x)| ≤ D)
    (hC : (∑ i, C i) ≤ M / a) (hD : D ≤ M / a ^ 2)
    {α : ℝ≥0} (hα1 : (α : ℝ) ≤ 1) :
    let metric : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
    @H2.boundedHolderNorm (ControlCarrier N) metric α univ f ≤
      ENNReal.ofReal (M + 2 * M / a ^ (α : ℝ)) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G H.norm H.constant_one H.symmetric
  apply scaled_cutoff_holderNorm_le (X := ControlCarrier N)
    (f := fun x : ControlCarrier N => f x) hM ha hα1 hsup
  intro x y
  have hv := global_meanValue_of_controlNorm H hf hfirst hdrift y x
  rw [← gaugeMetric_controlDistance G H y x] at hv
  change |f x - f y| ≤ dist y x * (∑ i, C i) + dist y x ^ 2 * D at hv
  rw [dist_comm y x] at hv
  calc
    _ ≤ dist x y * (∑ i, C i) + dist x y ^ 2 * D := hv
    _ ≤ dist x y * (M / a) + dist x y ^ 2 * (M / a ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hC dist_nonneg)
        (mul_le_mul_of_nonneg_left hD (sq_nonneg _))
    _ = M * (dist x y / a + (dist x y / a) ^ 2) := by ring

end RothschildStein.H3
