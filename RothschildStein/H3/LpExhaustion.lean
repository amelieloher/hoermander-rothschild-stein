-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- Monotone exhaustion of an Lp norm, allowing an infinite
limit norm. This is the monotone convergence step in BB pp. 356–357 and
Definition 8.41, p. 371. -/
theorem eLpNorm_iUnion_of_directed {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) (f : X → E) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (s : ℕ → Set X)
    (hd : Directed (· ⊆ ·) s)
    (hf : AEStronglyMeasurable f (μ.restrict (⋃ n, s n))) :
    eLpNorm f p (μ.restrict (⋃ n, s n)) =
      ⨆ n, eLpNorm f p (μ.restrict (s n)) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hfi (n : ℕ) : AEStronglyMeasurable f (μ.restrict (s n)) :=
    hf.mono_measure (Measure.restrict_mono_set μ (subset_iUnion s n))
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hfi _)]
  rw [setLIntegral_iUnion_of_directed (fun x => ‖f x‖ₑ ^ p.toReal) hd]
  exact (ENNReal.orderIsoRpow (1 / p.toReal) (by positivity)).map_iSup _

end RothschildStein.H3
