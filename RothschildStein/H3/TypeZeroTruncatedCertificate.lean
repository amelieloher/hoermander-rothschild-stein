-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffKernelClass
public import RothschildStein.H3.RadialCutoffGeometry
public import RothschildStein.H3.TypeZeroShells
public import RothschildStein.H3.LocalKernelSetting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.H3

/-- Assemble the actual radial truncation certificate from the
proved cutoff kernel class and type-zero shell cancellation. -/
theorem typeZero_truncatedKernelFacts_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {k : (Fin N → ℝ) → ℝ} (hk : TypeZero G C.norm k) :
    let _metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G C.norm C.constant_one C.symmetric
    let m := (volume {z : Fin N → ℝ | C.norm z < 1}).toReal
    TruncatedKernelFacts volume (m * kernelDerivativeBound C.norm k 1)
      (m * cutoffKernelSmoothConstant C.norm Y (-(G.homogeneousDimension : ℝ)) 2 1 *
        kernelDerivativeBound C.norm k 1)
      (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y) := by
  let _metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  let χ : (Fin N → ℝ) → ℝ := fun z => radialCutoff (C.norm z)
  have hχ : Measurable χ := (radialCutoff_lipschitz.continuous.comp C.norm.gauge.1).measurable
  have hmod (a b : Fin N → ℝ) : |χ a - χ b| ≤ 1 * G2.gaugeDistance G C.norm a b := by
    have h := radialCutoff_lipschitz.dist_le_mul (C.norm a) (C.norm b)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    exact h.trans (by simpa only [one_mul] using
      homogeneousNorm_sub_le_gaugeDistance C.norm C.constant_one C.symmetric a b)
  have hsupp (z : Fin N → ℝ) (hz : (2 : ℝ) < C.norm z) : χ z = 0 :=
    radialCutoff_eq_zero hz.le
  have hclass := cutoffGroupKernel_kernelClass_of_controlNorm C hY hhomY hk.smooth
    (show (0 : ℝ) ≤ 0 from le_rfl)
    (show (0 : ℝ) ≤ G.homogeneousDimension from Nat.cast_nonneg _)
    (by simpa only [zero_sub] using hk.homogeneous)
    (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
    hχ (fun z => radialCutoff_bounds (C.norm z)) hmod hsupp
  have heq : (fun x y : ControlCarrier N => cutoffGroupKernel G χ k x y) =
      (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y) := by
    funext x y
    exact mul_comm _ _
  dsimp only at hclass ⊢
  rw [heq] at hclass
  refine ⟨by simpa only [zero_sub] using hclass, ?_, ?_⟩
  · intro x y hxy
    exact truncatedKernel_eq_zero G C.norm k x y hxy
  · intro x a b ha hab
    exact hk.truncatedKernel_shell_zero G x ha hab

end RothschildStein.H3
