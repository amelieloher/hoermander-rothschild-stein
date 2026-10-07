-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CoordinateMultilinearBound
public import Mathlib.Analysis.Calculus.ContDiff.Basic
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Coordinate values of the ambient jet in standard coordinate directions. -/
def CoordinateFieldJetBudget {a N : ℕ} (Ω : Set (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) (R : ℕ) (B : ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ i k, k ≤ R → ∀ f : Fin k → Fin N, ∀ j : Fin N,
    |iteratedFDeriv ℝ k (X i) x (fun l => Pi.single (f l) (1 : ℝ)) j| ≤ B

/-- The numerical dimension factor converts coordinate jets to ambient jets. -/
theorem norm_field_jets_le_of_coordinate_budget {a N R : ℕ}
    (Ω : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    {B : ℝ} (hB : 0 ≤ B) (h : CoordinateFieldJetBudget Ω X R B) :
    ∀ x ∈ Ω, ∀ i k, k ≤ R →
      ‖iteratedFDeriv ℝ k (X i) x‖ ≤ (max 1 (N : ℝ))^R*B := by
  intro x hx i k hk
  have he := norm_multilinear_le_coordinate_budget (iteratedFDeriv ℝ k (X i) x) hB
    (fun f => (pi_norm_le_iff_of_nonneg hB).mpr (fun j => by
      simpa only [Real.norm_eq_abs] using h x hx i k hk f j))
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ hB
  exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (N : ℝ)) k).trans
    (pow_le_pow_right₀ (le_max_left 1 (N : ℝ)) hk)
end RothschildStein.G3
