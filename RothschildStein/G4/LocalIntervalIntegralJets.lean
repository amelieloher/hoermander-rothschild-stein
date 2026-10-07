-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalCompactIntegralJets
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.G4

universe u

/-- Finite parameter jets commute with the unit-interval remainder
estimate on a common local smooth domain. The bound uses the actual
integrand jets, including the endpoints (BB pp. 441–443). -/
theorem norm_local_interval_integral_jet_le {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set (E × ℝ)} (hS : IsOpen S) (G : E × ℝ → F)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) (x : E)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ S) (n : ℕ) {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y => G (y, t)) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ t in (0 : ℝ)..1, G (y, t)) x‖ ≤ M := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact norm_local_compact_parameter_integral_jet_le hS G hG x hsegment n hbound

end RothschildStein.G4
