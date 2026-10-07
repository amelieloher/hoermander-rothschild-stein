-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Comparing constants by integrating over a common set.
This is the integral triangle inequality used in BB Lemmas 7.40 and 7.44. -/
theorem oscillation_constants_comparison {μ : Measure X} {A B : Set X}
    (hAB : A ⊆ B) (hB : μ B < ⊤) {u : X → ℝ} (hu : IntegrableOn u B μ)
    (c d : ℝ) :
    |c - d| * (μ A).toReal ≤ integralOscillation (μ.restrict A) u c +
      integralOscillation (μ.restrict B) u d := by
  let : IsFiniteMeasure (μ.restrict B) := ⟨by simpa using hB⟩
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using (measure_mono hAB).trans_lt hB⟩
  have hcu := (hu.mono_set hAB).sub (integrable_const c)
  have hdu := hu.sub (integrable_const d)
  have h := integral_mono (integrable_const |c - d|)
    (hcu.abs.add (hdu.mono_set hAB).abs)
    (fun y => show |c - d| ≤ |u y - c| + |u y - d| by
      have ht := abs_add_le (c - u y) (u y - d)
      have he : (c - u y) + (u y - d) = c - d := by ring
      rw [he, abs_sub_comm c (u y)] at ht
      exact ht)
  dsimp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_add (show IntegrableOn (fun y => |u y - c|) A μ from hcu.abs)
    (show IntegrableOn (fun y => |u y - d|) A μ from (hdu.mono_set hAB).abs),
    integral_const, smul_eq_mul] at h
  have hs := setIntegral_mono_set hdu.abs
    (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ hAB)
  change _ ≤ ∫ y in A, |u y - c| ∂μ + ∫ y in B, |u y - d| ∂μ
  simp only [measureReal_def, Measure.restrict_apply_univ] at h
  dsimp only [Pi.sub_apply] at hs
  nlinarith
end RothschildStein.H2
