-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalKernelSetting
public import RothschildStein.H3.UnitSourceIntegralSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Origin control-metric distance is the homogeneous norm itself. -/
theorem gaugeMetric_dist_zero (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (x : ControlCarrier N) :
    let _localMetric := gaugeMetric G ν h1 hsym
    dist x 0 = ν x := by
  change ν (G.mul (G.inv 0) x) = ν x
  rw [G2.inv_zero]
  exact congrArg ν (G2.zero_mul G x)

/-- On unit-supported sources the two localization cutoffs and the zero
fractional kernel disappear exactly from the H2 integrand. -/
theorem localKernelData_unit_source_integrand (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (k u : ControlCarrier N → ℝ)
    (H : let _localMetric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (hsu : ∀ y, 1 ≤ ν y → u y = 0) {x : ControlCarrier N} (hx : ν x < 1) :
    let _localMetric := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (truncatedKernel G ν k) H
    ∀ y : ControlCarrier N, Q.cutoffKernel x y * u y = truncatedKernel G ν k x y * u y := by
  classical
  let _localMetric := gaugeMetric G ν h1 hsym
  dsimp only
  intro y
  by_cases hy : u y = 0
  · simp only [hy, mul_zero]
  have hny : ν y < 1 := lt_of_not_ge fun h => hy (hsu y h)
  have hdx := gaugeMetric_dist_zero G ν h1 hsym x
  have hdy := gaugeMetric_dist_zero G ν h1 hsym y
  have hxU : (x : ControlCarrier N) ∈ ball 0 2 := by
    change dist (x : ControlCarrier N) 0 < 2
    rw [hdx]
    linarith
  have hyU : (y : ControlCarrier N) ∈ ball 0 2 := by
    change dist (y : ControlCarrier N) 0 < 2
    rw [hdy]
    linarith
  have hax : localizationCutoff (0 : ControlCarrier N) x = 1 :=
    localizationCutoff_eq_one 0 (by change dist (x : ControlCarrier N) 0 ≤ 1; rw [hdx]; exact hx.le)
  have hby : localizationCutoff (0 : ControlCarrier N) y = 1 :=
    localizationCutoff_eq_one 0 (by change dist (y : ControlCarrier N) 0 ≤ 1; rw [hdy]; exact hny.le)
  change (if (x : ControlCarrier N) ∈ ball 0 2 ∧ y ∈ ball 0 2 then
    localizationCutoff 0 x * (truncatedKernel G ν k x y + 0) * localizationCutoff 0 y else 0) * u y = _
  rw [ite_eq_left ⟨hxU, hyU⟩, hax, hby, add_zero, one_mul, mul_one]

/-- The H2 positive truncations are the full radial-kernel truncations
on a unit-supported source. -/
theorem localKernelData_unit_source_truncation (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (k u : ControlCarrier N → ℝ)
    (H : let _localMetric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (hsu : ∀ y, 1 ≤ ν y → u y = 0) {x : ControlCarrier N} (hx : ν x < 1) (ε : ℝ) :
    let _localMetric := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (truncatedKernel G ν k) H
    H2.truncatedIntegral volume (ball (0 : ControlCarrier N) 2) dist Q.cutoffKernel ε u x =
      ∫ y in {y | ε < G2.gaugeDistance G ν x y}, u y * truncatedKernel G ν k x y := by
  classical
  let _localMetric := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (truncatedKernel G ν k) H
  dsimp only
  change (∫ y in ball (0 : ControlCarrier N) 2 ∩ {y | ε < G2.gaugeDistance G ν x y},
    Q.cutoffKernel x y * u y) = _
  have he : (fun y => Q.cutoffKernel x y * u y) = fun y => u y * truncatedKernel G ν k x y := by
    funext y
    rw [localKernelData_unit_source_integrand G ν h1 hsym A S k u H hsu hx y, mul_comm]
  rw [he]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
  · exact (isOpen_lt continuous_const (ν.gauge.1.comp
      ((G2.continuous_mul G).comp ((G2.continuous_inv G).prodMk continuous_const)))).measurableSet
  · exact inter_subset_right
  · intro y hy
    have hyU : y ∉ ball (0 : ControlCarrier N) 2 := fun h => hy.2 ⟨h, hy.1⟩
    have hny : 2 ≤ ν y := by
      apply le_of_not_gt
      intro hn
      apply hyU
      change ν (G.mul (G.inv 0) y) < 2
      rw [G2.inv_zero, G2.zero_mul]
      exact hn
    rw [hsu y (by linarith), zero_mul]

end RothschildStein.H3
