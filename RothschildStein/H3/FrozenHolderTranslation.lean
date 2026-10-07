-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlHolderScaling
public import RothschildStein.H3.FrozenHolderMetricNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Left pullback preserves the exact fixed full scalar
Hölder norm on the inverse-image domain. -/
theorem fixed_holder_norm_left_pullback_eq_of_controlNorm {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X) (z : Fin N → ℝ) (a : ℝ≥0)
    (U : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ)
    (hf : holderENorm (controlDistance univ w X) a U f < ⊤) :
    holderENorm (controlDistance univ w X) a (G.mul z ⁻¹' U) (f ∘ G.mul z) =
      holderENorm (controlDistance univ w X) a U f := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  rw [frozen_holderENorm_eq_control_norm G w X C] at hf
  rw [frozen_holderENorm_eq_control_norm G w X C,
    frozen_holderENorm_eq_control_norm G w X C]
  exact control_holderNorm_leftTranslation G C.norm C.constant_one C.symmetric z a U f
    (H2.BoundedHolder.parts hf).2

end RothschildStein.H3
