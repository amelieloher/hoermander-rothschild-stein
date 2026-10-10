-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TimeAverageDerivatives

/-! # Lipschitz regularity of averages of essentially bounded curves

An essentially bounded locally Bochner-integrable curve has a Lipschitz integral primitive.
The one-sided time averages inherit Lipschitz bounds from differences of that primitive.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An essentially bounded locally integrable curve has a Lipschitz integral primitive. -/
theorem lipschitzWith_integral_of_ae_norm_le {u : ℝ → E}
    (hu : LocallyIntegrable u volume) {M : ℝ≥0} (hb : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) :
    LipschitzWith M (fun t => ∫ s in (0 : ℝ)..t, u s) := by
  have hi (a b : ℝ) : IntervalIntegrable u volume a b :=
    (hu.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm, Real.dist_eq]
  have he : (∫ x in t..s, u x) = (∫ x in (0 : ℝ)..s, u x) - ∫ x in (0 : ℝ)..t, u x :=
    eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t s))
  rw [← he]
  exact intervalIntegral.norm_integral_le_of_norm_le_const_ae (hb.mono fun _ ht _ => ht)

/-- Forward averages of an essentially bounded curve are Lipschitz, including zero averaging scale. -/
theorem lipschitzWith_forwardTimeAverage_of_ae_norm_le {u : ℝ → E}
    (hu : LocallyIntegrable u volume) {M : ℝ≥0} (hb : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) (h : ℝ) :
    LipschitzWith (‖h⁻¹‖₊ * (M + M)) (forwardTimeAverage h u) := by
  have hP := lipschitzWith_integral_of_ae_norm_le hu hb
  have hi (a b : ℝ) : IntervalIntegrable u volume a b :=
    (hu.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have he : forwardTimeAverage h u =
      (fun t => h⁻¹ • ((∫ s in (0 : ℝ)..t + h, u s) - ∫ s in (0 : ℝ)..t, u s)) := by
    funext t
    dsimp [forwardTimeAverage]
    congr 1
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hi 0 t) (hi t (t + h)))
  have hshift : LipschitzWith 1 (fun t : ℝ => t + h) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, add_sub_add_right_eq_sub]
    exact le_rfl
  rw [he]
  simpa only [Function.comp_def, one_mul, mul_one, Pi.sub_def] using
    (lipschitzWith_smul h⁻¹).comp ((hP.comp hshift).sub hP)

/-- At positive scale an average preserves the essential norm bound pointwise. -/
theorem norm_forwardTimeAverage_le_of_ae_norm_le {u : ℝ → E} {M : ℝ≥0}
    (hb : ∀ᵐ t ∂volume, ‖u t‖ ≤ M) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ‖forwardTimeAverage h u t‖ ≤ M := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := t) (b := t + h) (hb.mono fun _ ht _ => ht)
  simp only [forwardTimeAverage, norm_smul, Real.norm_eq_abs]
  calc
    |h⁻¹| * ‖∫ s in t..t + h, u s‖ ≤ |h⁻¹| * ((M : ℝ) * |(t + h) - t|) :=
      mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ = M := by
      rw [add_sub_cancel_left, abs_inv, abs_of_pos hh]
      field_simp [ne_of_gt hh]

end HeatKernel
