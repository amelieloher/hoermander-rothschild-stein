-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularProjection
public import Mathlib.Algebra.MvPolynomial.Variables

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- The polynomial triangularity condition makes each
vertical coefficient independent of its own and subsequent coordinates. -/
theorem triangular_polynomial_eval_eq {n m : ℕ} (l : Fin m)
    (p : MvPolynomial (Fin (n + m)) ℝ)
    (hp : ∀ j ∈ p.vars, j.val < n + l.val)
    {ξ η : Fin (n + m) → ℝ}
    (hprefix : ∀ j : Fin (n + m), j.val < n + l.val → ξ j = η j) :
    MvPolynomial.eval ξ p = MvPolynomial.eval η p := by
  apply MvPolynomial.eval₂Hom_congr' rfl
  · intro j hj _
    exact hprefix j (hp j hj)
  · rfl

/-- With a fixed base point, triangular polynomial evaluation
is determined by preceding vertical coordinates alone. -/
theorem triangular_join_polynomial_eval_eq {n m : ℕ} (l : Fin m)
    (p : MvPolynomial (Fin (n + m)) ℝ)
    (hp : ∀ j ∈ p.vars, j.val < n + l.val)
    (x : Fin n → ℝ) {v u : Fin m → ℝ}
    (hprefix : ∀ j : Fin m, j.val < l.val → v j = u j) :
    MvPolynomial.eval (joinPoint x v) p = MvPolynomial.eval (joinPoint x u) p := by
  apply triangular_polynomial_eval_eq l p hp
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k _
    simp only [joinPoint, Fin.addCases_left]
  · intro k hk
    simp only [Fin.val_natAdd] at hk
    simpa only [joinPoint, Fin.addCases_right] using hprefix k (by omega)

end RothschildStein.L1
