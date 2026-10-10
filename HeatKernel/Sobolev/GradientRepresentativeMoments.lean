-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm
public import HeatKernel.Sobolev.LebesgueMoments
import Mathlib.Tactic.Linter

/-! # Literal quadratic moments of gradient-space representatives -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace
namespace HeatKernel.Sobolev

/-- The two quadratic graph coordinates are the literal value moment and the
sum of the specified gradient moments, for any almost-everywhere representatives. -/
theorem gradientSpace_norms_sq_eq_integrals_of_ae_eq {N q : ℕ}
    (v : GradientSpace (N := N) ⊤ q)
    {f : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hf : v.fst =ᵐ[volume] f) (hg : ∀ i, v.snd i =ᵐ[volume] g i) :
    ‖v.fst‖^2 = ∫ x, f x^2 ∧ ‖v.snd‖^2 = ∫ x, ∑ i, (g i x)^2 := by
  have hmem : ∀ i, MemLp (g i) 2 volume := by
    intro i
    have hv : MemLp (v.snd i) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (v.snd i)
    exact hv.ae_eq (hg i)
  constructor
  · have h := norm_sq_eq_integral_sq_of_ae_eq v.fst
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hf)
    simpa only [Opens.coe_top, Measure.restrict_univ] using h
  · rw [PiLp.norm_sq_eq_of_L2,
      integral_finsetSum Finset.univ (fun i _ => (hmem i).integrable_sq)]
    apply Finset.sum_congr rfl
    intro i _
    have h := norm_sq_eq_integral_sq_of_ae_eq (v.snd i)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hg i)
    simpa only [Opens.coe_top, Measure.restrict_univ] using h

end HeatKernel.Sobolev
