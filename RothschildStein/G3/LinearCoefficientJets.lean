-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ParameterProjectionJets
public import Mathlib.Analysis.Calculus.FDeriv.Linear
@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem norm_linear_coefficient_jet_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ max ‖L x‖ ‖L‖ := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero] using le_max_left ‖L x‖ ‖L‖
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ L = fun _ => L := funext (fun y => L.fderiv)
    rw [hd]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using le_max_right ‖L x‖ ‖L‖
    | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply,norm_zero]
      exact (norm_nonneg _).trans (le_max_left _ _)
end RothschildStein.G3
