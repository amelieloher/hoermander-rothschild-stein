-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PolynomialLiftChains
public import Mathlib.Algebra.MvPolynomial.Variables
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Projection to an initial coordinate block without an arithmetic cast. -/
def prefixPoint {n N : ℕ} (h : n ≤ N) (ξ : Fin N → ℝ) : Fin n → ℝ :=
  fun j => ξ (Fin.castLE h j)

/-- Actual horizontal agreement and polynomial vertical coefficients using
only earlier coordinates; this is the coordinate form of a triangular lift. -/
def TriangularPolynomialRepresentation {a n N : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∃ h : n ≤ N,
    (∀ i ξ j, Y i ξ (Fin.castLE h j) = X i (prefixPoint h ξ) j) ∧
    ∀ i (j : Fin N), n ≤ j.val →
      ∃ P : MvPolynomial (Fin N) ℝ,
        (∀ ξ, Y i ξ j = MvPolynomial.eval ξ P) ∧
        ∀ k ∈ P.vars, k.val < j.val

/-- The initial field system has the trivial triangular representation. -/
theorem triangularPolynomialRepresentation_refl {a n : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) :
    TriangularPolynomialRepresentation X X := by
  refine ⟨le_rfl,?_,?_⟩
  · intro i ξ j
    rfl
  · intro i j hj
    omega
end RothschildStein.L1
