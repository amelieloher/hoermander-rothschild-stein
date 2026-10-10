-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HeatGenerator
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! # Spectral bounds for positive contractive resolvents

Positivity and the operator norm bound put the real spectrum in the unit interval, providing
the spectral hypothesis used in the heat construction.
-/

@[expose] public section
open Set Filter
open scoped Topology
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem spectrum_subset_Icc_of_isPositive_norm_le_one (R : E →L[ℂ] E)
    (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1) : spectrum ℝ R ⊆ Icc (0 : ℝ) 1 := by
  rcases subsingleton_or_nontrivial E with h | h
  · have : Subsingleton E := h
    simp only [spectrum.of_subsingleton, empty_subset]
  have : Nontrivial E := h
  intro r hr
  refine ⟨spectrum_nonneg_of_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hpos) hr, ?_⟩
  exact (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans hnorm)

end HeatKernel
