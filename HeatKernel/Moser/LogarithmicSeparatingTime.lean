-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Common separating times for countably many logarithmic mean representatives -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- Countably many representatives of the same literal mean agree at almost
every time in an interior window common to their intervals. -/
theorem ae_common_logarithmic_mean_time
    {m : ℕ → ℝ → ℝ} {M : ℝ → ℝ} {a b : ℕ → ℝ} {L R : ℝ}
    (hmean : ∀ n, m n =ᵐ[volume.restrict (Icc (a n) (b n))] M)
    (hwindow : ∀ n, Ioo L R ⊆ Icc (a n) (b n)) :
    ∀ᵐ τ ∂volume.restrict (Ioo L R), ∀ n, m n τ = M τ := by
  exact ae_all_iff.mpr fun n =>
    ae_restrict_of_ae_restrict_of_subset (hwindow n) (hmean n)

end HeatKernel
