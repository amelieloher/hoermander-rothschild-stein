-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionDifferenceTests

/-!
# Adjoint time averages

Backward averaging of a scalar test is adjoint to forward averaging of the
curve. Product integrability is stated explicitly for the two Fubini exchanges.
-/

@[expose] public section

open MeasureTheory Set

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Backward and forward time averages are adjoint under integrable translated pairings. -/
theorem integral_backwardTimeAverage_smul_eq {ψ : ℝ → ℝ} {F : ℝ → E} (h : ℝ)
    (hback : Integrable (fun z : ℝ × ℝ => ψ (z.2 - z.1) • F z.2)
      ((volume.restrict (uIoc 0 h)).prod volume))
    (hforward : Integrable (fun z : ℝ × ℝ => ψ z.2 • F (z.2 + z.1))
      ((volume.restrict (uIoc 0 h)).prod volume)) :
    (∫ t, backwardTimeAverage h ψ t • F t) =
      ∫ t, ψ t • forwardTimeAverage h F t := by
  have hb (t : ℝ) : (∫ s in t - h..t, ψ s) = ∫ r in 0..h, ψ (t - r) := by
    simpa only [sub_zero] using (intervalIntegral.integral_comp_sub_left (a := 0) (b := h) ψ t).symm
  have hf (t : ℝ) : (∫ s in t..t + h, F s) = ∫ r in 0..h, F (t + r) := by
    simpa only [add_zero, add_comm] using
      (intervalIntegral.integral_comp_add_left (a := 0) (b := h) F t).symm
  simp only [backwardTimeAverage, forwardTimeAverage, hb, hf,
    smul_eq_mul, mul_smul]
  simp_rw [smul_comm (ψ _) h⁻¹]
  rw [integral_smul, integral_smul]
  congr 1
  simp_rw [← intervalIntegral.integral_smul_const,
    ← intervalIntegral.integral_smul]
  rw [← intervalIntegral_integral_swap hback,
    ← intervalIntegral_integral_swap hforward]
  apply intervalIntegral.integral_congr
  intro r _
  exact integral_shifted_time_test ψ F r

end HeatKernel
