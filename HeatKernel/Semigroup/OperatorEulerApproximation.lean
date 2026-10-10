-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.BoundedHeatOperators
public import HeatKernel.Semigroup.EulerApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! # Euler approximation in operator norm

Uniform scalar convergence on the spectral interval passes through continuous functional
calculus. The resolvent approximants here are defined by their scalar multipliers.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem tendsto_cfc_implicitEulerMultiplier (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => (cfc (implicitEulerMultiplier t n) R : E →L[ℂ] E)) atTop
      (𝓝 (cfc (heatMultiplier t) R)) := by
  apply tendsto_cfc_fun ((tendstoUniformlyOn_implicitEulerMultiplier ht).mono hspec)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact ((continuousOn_resolventMultiplier (div_pos ht hn')).pow n).mono hspec

theorem tendsto_resolventMultiplier_cfc_pow (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => (cfc (resolventMultiplier (t / n)) R : E →L[ℂ] E) ^ n)
      atTop (𝓝 (cfc (heatMultiplier t) R)) := by
  apply (tendsto_cfc_implicitEulerMultiplier R hspec ht).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact cfc_pow _ n R ((continuousOn_resolventMultiplier (div_pos ht hn')).mono hspec) hR

end HeatKernel
