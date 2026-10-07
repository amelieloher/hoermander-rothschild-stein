-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {n : ℕ}

/-- The integral of a directional derivative of a compact
smooth function is zero (BB properties (a),(b), pp. 76,78). -/
theorem integral_compact_fderiv_eq_zero {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcf : HasCompactSupport f) (v : Fin n → ℝ) :
    (∫ x, fderiv ℝ f x v) = 0 := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdf : HasCompactSupport (fun x => fderiv ℝ f x v) :=
    hcf.of_isClosed_subset isClosed_closure (by
      apply closure_minimal _ isClosed_closure
      intro x hx
      by_contra hn
      exact hx (by
        change (fderiv ℝ f x) v = 0
        rw [fderiv_of_notMem_tsupport ℝ hn]
        rfl))
  have hdfi : Integrable (fun x => fderiv ℝ f x v) volume :=
    hdf.integrable_of_hasCompactSupport hcdf
  have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Fin n → ℝ => (1 : ℝ)) (g := f) (v := v) (μ := volume)
    (by simpa only [fderiv_const_apply,zero_apply,MulZeroClass.zero_mul]
      using! integrable_zero (Fin n → ℝ) ℝ volume)
    (by simpa only [one_mul] using hdfi)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hcf)
    (fun x _ => differentiableAt_const (c := (1 : ℝ)))
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
  simpa only [one_mul,fderiv_const_apply,zero_apply,
    MulZeroClass.zero_mul,integral_zero,neg_zero] using H

end RothschildStein.S
