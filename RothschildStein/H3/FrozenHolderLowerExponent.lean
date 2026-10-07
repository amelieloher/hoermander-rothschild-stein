-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FrozenHolderMetricNorm
public import RothschildStein.H3.HolderInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- A finite full control Hölder norm is finite at every
smaller nonnegative exponent, even on an unbounded domain. -/
theorem fixed_holder_lower_exponent_finite_of_controlNorm {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X)
    {a b : ℝ≥0} (ha : 0 < a) (hba : b ≤ a)
    (U : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ)
    (hf : holderENorm (controlDistance univ w X) a U f < ⊤) :
    holderENorm (controlDistance univ w X) b U f < ⊤ := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  rw [frozen_holderENorm_eq_control_norm G w X C a U f] at hf
  rw [frozen_holderENorm_eq_control_norm G w X C b U f]
  have hfinite : @H2.BoundedHolder (ControlCarrier N) metric a U f := hf
  have hsemi := @holderSemi_interpolation (ControlCarrier N) metric a b ha hba U f hfinite
  exact ENNReal.add_lt_top.mpr ⟨hfinite.parts.1, hsemi.trans_lt ENNReal.ofReal_lt_top⟩

end RothschildStein.H3
