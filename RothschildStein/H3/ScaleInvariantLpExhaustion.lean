-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GaugeLpExhaustion
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- A scale-invariant half-radius estimate loses its inverse-square
remainder at infinity and yields global Lp membership with the sharp limit. -/
theorem memLp_of_scaleInvariant_halfRadius_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν f : X → ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (A B : ℝ)
    (hb : ∀ R : ℝ, 0 < R →
      eLpNorm f p (μ.restrict {x | ν x < R / 2}) ≤
        ENNReal.ofReal (A + B * (R⁻¹) ^ 2)) :
    MemLp f p μ ∧ eLpNorm f p μ ≤ ENNReal.ofReal A := by
  have ht : Tendsto (fun R : ℝ => ENNReal.ofReal (A + B * (R⁻¹) ^ 2))
      atTop (𝓝 (ENNReal.ofReal A)) := by
    apply ENNReal.tendsto_ofReal
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.pow 2 |>.const_mul B))
  apply memLp_of_uniform_sublevel_bounds μ ν f hp0 hpt hf ENNReal.ofReal_lt_top
  intro n
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (2 * ((n : ℝ) + 1))] with R hR
  have hpos : 0 < R := by linarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hs : {x | ν x < (n : ℝ) + 1} ⊆ {x | ν x < R / 2} := by
    intro x hx
    change ν x < R / 2
    change ν x < (n : ℝ) + 1 at hx
    linarith
  exact (eLpNorm_mono_measure f (Measure.restrict_mono_set μ hs)).trans (hb R hpos)

end RothschildStein.H3
