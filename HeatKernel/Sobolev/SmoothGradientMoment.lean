-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.UniformTranslation
public import HeatKernel.Form.ZeroBoundaryCore
public import HeatKernel.Sobolev.LebesgueMoments
import Mathlib.Tactic

/-! # The horizontal gradient moment of a smooth graph representative -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A graph vector representing the horizontal derivatives has their exact quadratic moment. -/
theorem lintegral_horizontalGradientNorm_sq_eq_norm_snd {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (v : GradientSpace (N := N) ⊤ q) (f : (Fin N → ℝ) → ℝ)
    (hgrad : ∀ i, v.snd i =ᵐ[volume] fieldDerivative (X i) f) :
    (∫⁻ x, ENNReal.ofReal (horizontalGradientNorm X f x ^ 2)) =
      ENNReal.ofReal (‖v.snd‖ ^ 2) := by
  have hfi : ∀ i : Fin q, Integrable (fun x => (v.snd i x) ^ 2) volume := by
    intro i
    simpa only [Opens.coe_top, Measure.restrict_univ] using (Lp.memLp (v.snd i)).integrable_sq
  have heq : (fun x => horizontalGradientNorm X f x ^ 2) =ᵐ[volume]
      (fun x => ∑ i, (v.snd i x) ^ 2) := by
    filter_upwards [ae_all_iff.mpr hgrad] with x hx
    rw [horizontalGradientNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i]
    rfl
  have hi : Integrable (fun x => horizontalGradientNorm X f x ^ 2) volume :=
    (integrable_finsetSum Finset.univ fun i _ => hfi i).congr heq.symm
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_congr_ae heq,
    integral_finsetSum Finset.univ (fun i _ => hfi i), PiLp.norm_sq_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have H := norm_sq_eq_integral_sq_of_ae_eq (v.snd i)
    (Filter.Eventually.of_forall fun _ => rfl)
  simpa only [Opens.coe_top, Measure.restrict_univ] using H.symm

end HeatKernel.Sobolev
