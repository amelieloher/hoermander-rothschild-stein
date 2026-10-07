-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.G4

/-- Change of variables gives two-sided image measure estimates
on exactly the measurable box where injectivity and the Jacobian bound
hold (BB proof of Thm 9.12, p. 405). -/
theorem chart_image_volume_bounds {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) (f : (Fin n → ℝ) → (Fin n → ℝ))
    (D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hD : ∀ x ∈ S, HasFDerivAt f (D x) x) (hinj : InjOn f S)
    {c C : ℝ}
    (hlo : ∀ x ∈ S, c ≤ |(D x).det|) (hhi : ∀ x ∈ S, |(D x).det| ≤ C) :
    ENNReal.ofReal c * volume S ≤ volume (f '' S) ∧
      volume (f '' S) ≤ ENNReal.ofReal C * volume S := by
  have heq := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hS
    (fun x hx => (hD x hx).hasFDerivWithinAt) hinj (fun _ => (1 : ℝ≥0∞))
  simp only [mul_one, lintegral_one, Measure.restrict_apply_univ] at heq
  rw [heq]
  constructor
  · have h := lintegral_mono_ae (μ := volume.restrict S) (f := fun _ => ENNReal.ofReal c)
      (g := fun x => ENNReal.ofReal |(D x).det|) (by
        filter_upwards [ae_restrict_mem hS] with x hx
        exact ENNReal.ofReal_le_ofReal (hlo x hx))
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  · have h := lintegral_mono_ae (μ := volume.restrict S) (f := fun x => ENNReal.ofReal |(D x).det|)
      (g := fun _ => ENNReal.ofReal C) (by
        filter_upwards [ae_restrict_mem hS] with x hx
        exact ENNReal.ofReal_le_ofReal (hhi x hx))
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h

end RothschildStein.G4
