-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.MaximumOperator
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RothschildStein.H1
variable {N q : ℕ}

/-- Scalar linearity of a field action, including the derivative
default at nondifferentiable points (BB pp. 249–250). -/
theorem fieldDerivative_const_mul (V : (Fin N → ℝ) → (Fin N → ℝ))
    (c : ℝ) (f : (Fin N → ℝ) → ℝ) :
    fieldDerivative V (fun x => c * f x) = fun x => c * fieldDerivative V f x := by
  funext x
  unfold fieldDerivative
  change fderiv ℝ (c • f) x (V x) = _
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]

/-- Addition for one differentiable field action (BB pp. 249–250). -/
theorem fieldDerivative_add_at (V : (Fin N → ℝ) → (Fin N → ℝ))
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fieldDerivative V (f + g) x = fieldDerivative V f x + fieldDerivative V g x := by
  simp only [fieldDerivative, fderiv_add hf hg, add_apply]

/-- The first field action is differentiable under precisely
C2 regularity of the function and C1 regularity of the field (BB p. 249). -/
theorem differentiableAt_fieldDerivative
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hV : DifferentiableAt ℝ V x) :
    DifferentiableAt ℝ (fieldDerivative V f) x :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one).clm_apply hV

/-- Addition for a squared field action at a C2 point
(BB p. 249). -/
theorem fieldSquare_add_at
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hV : DifferentiableAt ℝ V x) :
    fieldDerivative V (fieldDerivative V (f + g)) x =
      fieldDerivative V (fieldDerivative V f) x + fieldDerivative V (fieldDerivative V g) x := by
  have he : fieldDerivative V (f + g) =ᶠ[𝓝 x] fieldDerivative V f + fieldDerivative V g := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hy'
    exact fieldDerivative_add_at V (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))
  change fderiv ℝ (fieldDerivative V (f + g)) x (V x) = _
  rw [he.fderiv_eq]
  exact fieldDerivative_add_at V (differentiableAt_fieldDerivative hf hV)
    (differentiableAt_fieldDerivative hg hV)

/-- Scalar linearity of the sum-of-squares operator
(BB pp. 249–250). -/
theorem sumSquares_const_mul
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : ℝ) (f : (Fin N → ℝ) → ℝ) :
    sumSquaresWithDrift X (fun x => c * f x) = fun x => c * sumSquaresWithDrift X f x := by
  funext x
  simp only [sumSquaresWithDrift, fieldDerivative_const_mul, Finset.mul_sum, mul_add]

/-- Local addition for the sum-of-squares operator
(BB pp. 249–250). -/
theorem sumSquares_add_at
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hX : ∀ i : Fin q, DifferentiableAt ℝ (X i.succ) x) :
    sumSquaresWithDrift X (f + g) x = sumSquaresWithDrift X f x + sumSquaresWithDrift X g x := by
  unfold sumSquaresWithDrift
  rw [fieldDerivative_add_at (X 0) (hf.differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))]
  simp_rw [fieldSquare_add_at hf hg (hX _)]
  rw [Finset.sum_add_distrib]
  ring

end RothschildStein.H1
