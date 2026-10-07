-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.DualTruncation
public import RothschildStein.H2.DualRoot

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The clamped absolute value is in every Lᵖ space of a
finite measure (BB p. 326). -/
theorem absoluteClamp_memLp (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {n : ℝ} (hn : 0 ≤ n) (p : ℝ≥0∞) :
    MemLp (fun x => min |f x| n) p μ := by
  have hm : Measurable (fun x => min |f x| n) := by
    simpa only [Real.norm_eq_abs] using hf.norm.min measurable_const
  apply MemLp.of_bound hm.aestronglyMeasurable n
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (le_min (abs_nonneg _) hn)]
  exact min_le_right _ _

/-- The q-norm of the dual test is the q-th root of the
finite clamped p-th moment (BB p. 326). -/
theorem dualTruncation_norm_moment (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {p q n : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hn : 0 ≤ n) (hpq : (p - 1) * q = p) :
    moment μ p (fun x => min |f x| n) < ∞ ∧
      (eLpNorm (dualTruncation f p n) (ENNReal.ofReal q) μ).toReal =
        (moment μ p (fun x => min |f x| n)).toReal ^ (1 / q) := by
  have hm : Measurable (fun x => min |f x| n) := by
    simpa only [Real.norm_eq_abs] using hf.norm.min measurable_const
  have hfin := (memLp_iff_moment_lt_top μ hm.aemeasurable hp).mp
    (absoluteClamp_memLp μ hf hn (ENNReal.ofReal p))
  refine ⟨hfin, ?_⟩
  rw [eLpNorm_eq_moment_rpow μ (measurable_dualTruncation hf p n).aemeasurable hq,
    ENNReal.toReal_rpow]
  congr 2
  apply lintegral_congr
  intro x
  rw [dualTruncation_abs_rpow hn hpq, abs_of_nonneg (le_min (abs_nonneg _) hn)]

end RothschildStein.H2
