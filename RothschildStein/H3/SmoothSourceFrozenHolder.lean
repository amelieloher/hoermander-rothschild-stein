-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactSourceControlHolder
public import RothschildStein.H3.HolderCutoffProduct
public import RothschildStein.H3.FrozenHolderMetricNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- A smooth compact source supported in a bounded control
ball has finite full global fixed Hölder norm in every exponent at most one. -/
theorem smooth_source_global_holder_finite_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G driftWeight X)
    (a : ℝ≥0) (ha : a ≤ 1) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {x | C.norm x < R}) :
    holderENorm (controlDistance univ driftWeight X) a univ f < ⊤ := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  let E := ball (0 : ControlCarrier N) R
  have hsE : tsupport f ⊆ E := by
    intro x hx
    change C.norm (G.mul (G.inv 0) x) < R
    rw [G2.inv_zero, G2.zero_mul]
    exact hs hx
  have hb := compact_source_boundedHolder_control_ball G C.norm C.constant_one C.symmetric
    R f (hf.of_le (by simp)) hc ha
  rw [frozen_holderENorm_eq_control_norm G driftWeight X C]
  rw [boundedHolderNorm_global_eq_of_controlNorm C isOpen_ball hc hsE]
  exact hb

end RothschildStein.H3
