-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupSetting
public import RothschildStein.H3.LocalizationCutoff
public import RothschildStein.H3.ZeroKernel
public import RothschildStein.H2.KernelRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Global estimates for a truncated kernel. In the homogeneous group
setting, A and S are respectively m Λ₀ and 3 c₁ Λ₁. -/
structure TruncatedKernelFacts (μ : Measure X) (A S : ℝ) (K : X → X → ℝ) : Prop where
  kernel : H2.KernelClass μ univ 1 0 A S K
  support : ∀ x y, 2 ≤ dist x y → K x y = 0
  shells : ∀ x a b, 0 < a → a < b →
    (∫ y in {y | a < dist x y ∧ dist x y < b}, K x y ∂μ) = 0

/-- The truncation distance is the metric itself, with both comparison
constants exactly one (BB pp. 357–359). -/
def metricTruncDist [SecondCountableTopology X] (D : H2.LocDoubling X) : H2.TruncDist D where
  d' := dist
  θ₁ := 1
  θ₂ := 1
  θ₁_pos := zero_lt_one
  θ₁_le := le_rfl
  comp := fun _ _ _ _ => by simp
  meas := continuous_dist.measurable
  symm := dist_comm

/-- The truncated-kernel hypotheses hold on the radius-two localization
ball, and the fractional piece is zero. -/
def localKernelData_of_truncatedKernelFacts {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S K) :
    letI := gaugeMetric G ν h1 hsym
    H2.LocalKernelData (groupSetting G ν h1 hsym)
      (metricTruncDist (groupSetting G ν h1 hsym)) := by
  letI := gaugeMetric G ν h1 hsym
  refine {
    z := 0
    center := by change dist (0 : ControlCarrier N) 0 < 1; simp
    R := 2
    radius_pos := by norm_num
    radius_lt := by change (2 : ℝ) < 3; norm_num
    R' := 2
    support_radius_pos := by norm_num
    support_radius_le := by norm_num [metricTruncDist]
    a := localizationCutoff 0
    b := localizationCutoff 0
    Lₐ := 2
    Lᵦ := 2
    cutoff_a := localizationCutoff_kernelCutoff 0
    cutoff_b := localizationCutoff_kernelCutoff 0
    β₀ := 1
    β := 1
    ν := 1
    ν_pos := zero_lt_one
    A₀ := A
    S₀ := S
    A₁ := 0
    S₁ := 0
    K₀ := K
    K₁ := fun _ _ => 0
    singular := H.kernel.restrict isOpen_ball.measurableSet (subset_univ _)
    fractional := zeroKernel_class volume isOpen_ball.measurableSet zero_lt_one le_rfl
      zero_le_one
    support₀ := fun x _ y _ h => H.support x y h
    support₁ := fun _ _ _ _ _ => rfl
    vanishing := ?_
  }
  intro x hx a b ha hab hb
  have hx2 : dist x (0 : ControlCarrier N) < 2 := hx
  have heq : ball (0 : ControlCarrier N) (2 * 2) ∩
      {y | a < dist x y ∧ dist x y < b} = {y | a < dist x y ∧ dist x y < b} := by
    apply inter_eq_right.mpr
    intro y hy
    change dist y 0 < 2 * 2
    have hxy : dist y x < b := by simpa only [dist_comm y x] using hy.2
    exact (dist_triangle y x 0).trans_lt (by linarith)
  change (∫ y in ball (0 : ControlCarrier N) (2 * 2) ∩
    {y | a < dist x y ∧ dist x y < b}, K x y) = 0
  rw [heq]
  exact H.shells x a b ha hab

end RothschildStein.H3
