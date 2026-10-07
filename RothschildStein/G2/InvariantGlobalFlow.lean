-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantFiniteTimeCurve
public import RothschildStein.G2.GlobalCurveFromFiniteIntervals

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Global completeness of every left-invariant field. -/
theorem exists_global_leftField_curve (v : Fin N → ℝ) :
    ∃ γ : ℝ → (Fin N → ℝ), γ 0 = 0 ∧
      IsIntegralCurve γ (fun _ => leftField G v) :=
  exists_global_integralCurve_of_finite_intervals (leftField G v)
    (contDiff_leftField G v) 0 (fun _ hT => exists_leftField_curve_on_interval G v hT)

/-- The exponential curve through the group identity. -/
def leftExponential (v : Fin N → ℝ) : ℝ → (Fin N → ℝ) :=
  (exists_global_leftField_curve G v).choose

theorem leftExponential_zero (v : Fin N → ℝ) : leftExponential G v 0 = 0 :=
  (exists_global_leftField_curve G v).choose_spec.1

theorem leftExponential_integralCurve (v : Fin N → ℝ) :
    IsIntegralCurve (leftExponential G v) (fun _ => leftField G v) :=
  (exists_global_leftField_curve G v).choose_spec.2

theorem continuous_leftExponential (v : Fin N → ℝ) : Continuous (leftExponential G v) :=
  continuous_iff_continuousAt.mpr fun t => (leftExponential_integralCurve G v t).continuousAt

/-- Left translations give the global flow through every starting point. -/
theorem leftExponential_translated_integralCurve (v x : Fin N → ℝ) :
    IsIntegralCurve (fun t => G.mul x (leftExponential G v t))
      (fun _ => leftField G v) := by
  intro t
  have h := ((contDiff_leftTranslation G x).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t (leftExponential_integralCurve G v t)
  simpa only [Function.comp_def,leftField_invariant G v x (leftExponential G v t)] using h

/-- Simultaneous global flows with the precise finite-family flow statement. -/
theorem exists_global_leftInvariant_flows {m : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, IsLeftInvariantField G (X i)) :
    ∃ E : Fin m → ℝ → (Fin N → ℝ),
      (∀ i, Continuous (E i)) ∧ (∀ i, E i 0 = 0) ∧
      ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => X i) := by
  refine ⟨fun i => leftExponential G (X i 0),fun i => continuous_leftExponential G _,
    fun i => leftExponential_zero G _,?_⟩
  intro i x
  have h := leftExponential_translated_integralCurve G (X i 0) x
  rw [← (hX i).eq_leftField G] at h
  exact h

end RothschildStein.G2
