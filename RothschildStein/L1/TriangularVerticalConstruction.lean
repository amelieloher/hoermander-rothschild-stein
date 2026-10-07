-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularExistence
public import RothschildStein.L1.TriangularRightSide
public import RothschildStein.L1.CoordinateAbsoluteContinuity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace RothschildStein.L1

/-- Triangular polynomials lift an already given
continuous base curve, with bounded measurable controls, throughout the
whole compact time interval. Each vertical coordinate is absolutely
continuous and satisfies the actual polynomial vertical equation. -/
theorem exists_triangular_vertical_curve {q n m : ℕ} {a b : ℝ}
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hP : ∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val)
    (γ : ℝ → (Fin n → ℝ)) (hγ : ContinuousOn γ (uIcc a b))
    (c : Fin q → ℝ → ℝ) (C : Fin q → ℝ)
    (hc : ∀ i, AEMeasurable (c i) (volume.restrict (uIcc a b)))
    (hbound : ∀ i, ∀ᵐ t ∂volume.restrict (uIcc a b), |c i t| ≤ C i)
    (z : Fin m → ℝ) :
    ∃ v : ℝ → (Fin m → ℝ),
      (∀ l, AbsolutelyContinuousOnInterval (fun t => v t l) a b) ∧ v a = z ∧
      ∀ l, ∀ᵐ t ∂volume, t ∈ uIcc a b →
        HasDerivAt (fun t => v t l)
          (∑ i, c i t * MvPolynomial.eval (joinPoint (γ t) (v t)) (P i l)) t := by
  let F : Fin m → ℝ → (Fin m → ℝ) → ℝ := fun l t v =>
    ∑ i, c i t * MvPolynomial.eval (joinPoint (γ t) v) (P i l)
  have hF : ∀ l t v u, (∀ j : Fin m, j.val < l.val → v j = u j) →
      F l t v = F l t u := by
    intro l t v u hprefix
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact triangular_join_polynomial_eval_eq l (P i l) (hP i l) (γ t) hprefix
  have hInt : ∀ l (v : ℝ → (Fin m → ℝ)),
      (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) a b) →
      IntervalIntegrable (fun t => F l t (v t)) volume a b := by
    intro l v hv
    have hpacked : ContinuousOn (fun t => joinPoint (γ t) (v t)) (uIcc a b) := by
      apply continuousOn_pi.mpr
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro k
        simpa only [joinPoint, Fin.addCases_left] using continuousOn_pi.mp hγ k
      · intro k
        simpa only [joinPoint, Fin.addCases_right] using (hv k).continuousOn
    exact triangular_vertical_rhs_intervalIntegrable P l _ hpacked c C hc hbound
  exact exists_triangular_ac_solution_of_integrable F hF hInt z

end RothschildStein.L1
