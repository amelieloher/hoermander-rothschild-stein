-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.MeanOscillation
public import HeatKernel.Poincare.TranslationPairs
public import Mathlib.MeasureTheory.Measure.Prod

/-! Integrated Jensen bounds and the translation change of variables for point pairs. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set RothschildStein
open scoped ENNReal

namespace HeatKernel

/-- Tonelli and left Haar invariance replace pairs in a ball by increments in its doubled
identity ball. The integrand is nonnegative, so no finite-integral hypothesis is needed. -/
theorem lintegral_pairwise_le_translation_pairs {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 ≤ r)
    {F : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞}
    (hF : ∀ y, Measurable (F y))
    (htranslated : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      F p.1 (G.mul p.1 p.2))) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ∫⁻ z in horizontalBall (G.horizontalFields hq) x r, F y z) ≤
    ∫⁻ z in horizontalBall (G.horizontalFields hq) 0 (2 * r),
      ∫⁻ y in horizontalBall (G.horizontalFields hq) x r, F y (G.mul y z) := by
  calc
    (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
        ∫⁻ z in horizontalBall (G.horizontalFields hq) x r, F y z) ≤
        ∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
          ∫⁻ z in horizontalBall (G.horizontalFields hq) 0 (2 * r), F y (G.mul y z) := by
      apply lintegral_mono_ae
      exact ae_restrict_of_forall_mem (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet
        (fun y hy => lintegral_pair_le_lintegral_translation G hq hqpos hspan hr hy (hF y))
    _ = _ := lintegral_lintegral_swap htranslated.aemeasurable

end HeatKernel
