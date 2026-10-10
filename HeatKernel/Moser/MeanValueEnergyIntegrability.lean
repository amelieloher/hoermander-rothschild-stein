-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSpatialSobolev
public import HeatKernel.Moser.MeanValueSobolevMoments
public import HeatKernel.Sobolev.HorizontalSobolevVolume
public import Mathlib.MeasureTheory.Function.L2Space
public import HeatKernel.Bridge.ZeroBoundaryWeakCutoffTimeIdentity
import Mathlib.Tactic

/-! # Finite spacetime energy and quadratic spatial moments -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A square-integrable energy curve has an integrable scaled spatial energy. -/
theorem integrable_zeroBoundary_scaled_energy {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (τ : Measure ℝ) {v : ℝ → zeroBoundaryGraph U X} (hv : MemLp v 2 τ) (r : ℝ) :
    Integrable (fun t => r ^ 2 * ‖(v t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
      ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) τ := by
  have hc : Continuous (fun z : zeroBoundaryGraph U X =>
      r ^ 2 * ‖(z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) := by fun_prop
  have hmajor := ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv).const_mul
    (r ^ 2 + 1)
  apply hmajor.mono' (hc.comp_aestronglyMeasurable hv.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hf : ‖(v t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ ‖v t‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (WithLp.norm_fst_le _ (v t : GradientSpace (N := N) ⊤ q)) 2
  have hg : ‖(v t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤ ‖v t‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (WithLp.norm_snd_le _ (v t : GradientSpace (N := N) ⊤ q)) 2
  nlinarith [sq_nonneg r]

end HeatKernel
