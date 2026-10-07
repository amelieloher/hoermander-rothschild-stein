-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.JetRemainder
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Basic
@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem norm_iterated_derivative_flattening
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (x : E) (k r : ℕ) :
    ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ r f) x‖ =
      ‖iteratedFDeriv ℝ (k+r) f x‖ := by
  induction r generalizing k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    simp
  | succ r ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
      (F := E →L[ℝ] E [×r]→L[ℝ] F) (G := E [×(r+1)]→L[ℝ] F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => E) F).symm]
    rw [norm_iteratedFDeriv_fderiv,ih]
    have hindex : k+1+r = k+(r+1) := by omega
    rw [hindex]
end RothschildStein.G3
