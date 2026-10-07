-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactUnitPrincipalValueEstimate
public import RothschildStein.H3.TypeZeroGlobalLpFromUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The global compact-source estimate follows from the scaled
truncated-kernel bounds. -/
theorem compactPrincipalValue_global_eLpNorm_bound_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (k : ControlCarrier N → ℝ)
    (H : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (fun x y : ControlCarrier N => truncatedKernel G ν k x y))
    (Ht : let _metric := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume ((kernelDerivativeBound ν k 1) * A) ((kernelDerivativeBound ν k 1) * S) (fun x y : ControlCarrier N => truncatedKernel G ν k y x))
    (hk : TypeZero G ν k) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : ControlCarrier N → ℝ) (hu : ContDiff ℝ 1 (fun y : Fin N → ℝ => u y))
    (hs : HasCompactSupport u) :
    let _metric := gaugeMetric G ν h1 hsym
    MemLp (fun x : ControlCarrier N => H1.principalValueConvolution G ν k u x)
        (ENNReal.ofReal p) volume ∧
    eLpNorm (fun x : ControlCarrier N => H1.principalValueConvolution G ν k u x)
        (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal ((kernelDerivativeBound ν k 1) * normalizedLocalLpConstant G ν h1 hsym A S hA hS p) +
        ENNReal.ofReal (kernelDerivativeBound ν k 1) * volume {x | 1 ≤ ν x ∧ ν x ≤ 2}) *
          eLpNorm u (ENNReal.ofReal p) volume := by
  let _metric := gaugeMetric G ν h1 hsym
  let C : ℝ≥0∞ :=
    ENNReal.ofReal ((kernelDerivativeBound ν k 1) *
      normalizedLocalLpConstant G ν h1 hsym A S hA hS p) +
    ENNReal.ofReal (kernelDerivativeBound ν k 1) *
      volume {x : ControlCarrier N | 1 ≤ ν x ∧ ν x ≤ 2}
  have hballVolume : (volume : Measure (Fin N → ℝ)) {x | ν x ≤ 2} < ∞ :=
    (G2.isCompact_gauge_le ν.gauge 2).measure_lt_top
  have hann : volume {x : ControlCarrier N | 1 ≤ ν x ∧ ν x ≤ 2} < ∞ :=
    (measure_mono (show {x : ControlCarrier N | 1 ≤ ν x ∧ ν x ≤ 2} ⊆
      {x | ν x ≤ 2} from fun _ hx => hx.2)).trans_lt
        hballVolume
  have hC : C < ∞ := ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hann⟩
  have hball : ball (0 : ControlCarrier N) 1 = {x | ν x < 1} := by
    ext x
    change ν (G.mul (G.inv 0) x) < 1 ↔ ν x < 1
    rw [G2.inv_zero, G2.zero_mul]
  have hunit : ∀ v : (Fin N → ℝ) → ℝ, ContDiff ℝ 1 v → HasCompactSupport v →
      (∀ x, 1 ≤ ν x → v x = 0) →
      eLpNorm (H1.principalValueConvolution G ν k v) (ENNReal.ofReal p)
        (volume.restrict {x | ν x < 1}) ≤ ENNReal.ofReal C.toReal *
          eLpNorm v (ENNReal.ofReal p) volume := by
    intro v hv hsv hsvu
    rw [ENNReal.ofReal_toReal hC.ne]
    simpa only [hball, C, ControlCarrier, controlCarrierMeasureSpace] using compactUnitPrincipalValue_eLpNorm_bound_of_truncatedKernelFacts
      G ν h1 hsym A S hA hS k H Ht hk hp v hv hsv hsvu
  have h := hk.principalValue_global_compact_bound_of_unit G
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne' ENNReal.ofReal_ne_top
    C.toReal hunit hu hs
  rw [ENNReal.ofReal_toReal hC.ne] at h
  simpa only [C, ControlCarrier, controlCarrierMeasureSpace] using h

end RothschildStein.H3
