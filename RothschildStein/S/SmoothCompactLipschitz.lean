-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ContinuousTestProducts
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Const

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- Smooth compactly supported functions have a global
Euclidean Lipschitz constant, obtained from their compactly supported
continuous derivative (BB (2.15), p. 81; derivative-bound). -/
theorem exists_lipschitz_constant_of_smooth_compact
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ Λ : ℝ,0 ≤ Λ ∧ ∀ x y,|f x-f y| ≤ Λ*‖x-y‖ := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hd
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ f 0)).trans (hC 0)
  let L : ℝ≥0 := ⟨C,hC0⟩
  have hL : LipschitzWith L f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by simp)) (fun x => by exact_mod_cast hC x)
  refine ⟨C,hC0,fun x y => ?_⟩
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,L] using! hL.dist_le_mul x y

end RothschildStein.S
