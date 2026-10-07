-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.MeasurableControlIntegration
public import RothschildStein.L1.TriangularCoefficientDependence
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace RothschildStein.L1

/-- The polynomial lift coefficients give integrable
vertical right sides for any continuous packed curve and bounded
measurable controls. This applies at every successive integration stage. -/
theorem triangular_vertical_rhs_intervalIntegrable {q n m : ℕ} {a b : ℝ}
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (l : Fin m) (ξ : ℝ → (Fin (n + m) → ℝ))
    (hξ : ContinuousOn ξ (uIcc a b))
    (c : Fin q → ℝ → ℝ) (C : Fin q → ℝ)
    (hc : ∀ i, AEMeasurable (c i) (volume.restrict (uIcc a b)))
    (hbound : ∀ i, ∀ᵐ t ∂volume.restrict (uIcc a b), |c i t| ≤ C i) :
    IntervalIntegrable (fun t => ∑ i, c i t * MvPolynomial.eval (ξ t) (P i l))
      volume a b := by
  apply intervalIntegrable_control_sum c (fun i t => MvPolynomial.eval (ξ t) (P i l)) C hc hbound
  intro i
  exact (MvPolynomial.continuous_eval (p := P i l)).comp_continuousOn hξ

end RothschildStein.L1
