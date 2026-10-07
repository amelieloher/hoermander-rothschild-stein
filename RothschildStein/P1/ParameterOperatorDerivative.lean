-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorCoefficientCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Differentiate a jointly smooth finite operator
family in a parameter direction, keeping its fixed multi-index set.
The group variable is held fixed (BB Rem 11.9, p. 544). -/
def parameterOperatorDerivative (D : P → SmoothDifferentialOperator N)
    (indices : Finset (Fin N → ℕ))
    (hcoeff : ∀ a ∈ indices, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × (Fin N → ℝ) => (D z.1).coefficient a z.2))
    (p v : P) : SmoothDifferentialOperator N where
  indices := indices
  coefficient := fun a u => fderiv ℝ
    (fun z : P × (Fin N → ℝ) => (D z.1).coefficient a z.2) (p, u) (v, 0)
  smooth_coefficient := by
    intro a ha
    have hd := (contDiff_infty_iff_fderiv.mp (hcoeff a ha)).2
    exact (hd.clm_apply contDiff_const).comp (contDiff_const.prodMk contDiff_id)

/-- Differentiated coefficients remain jointly
smooth in parameters and group coordinates, at every derivative budget. -/
theorem parameterOperatorDerivative_joint_smooth
    (D : P → SmoothDifferentialOperator N) (indices : Finset (Fin N → ℕ))
    (hcoeff : ∀ a ∈ indices, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × (Fin N → ℝ) => (D z.1).coefficient a z.2))
    (v : P) (a : Fin N → ℕ) (ha : a ∈ indices) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : P × (Fin N → ℝ) =>
      (parameterOperatorDerivative D indices hcoeff z.1 v).coefficient a z.2) := by
  exact ((contDiff_infty_iff_fderiv.mp (hcoeff a ha)).2).clm_apply contDiff_const

/-- The coefficient is the actual parameter
Fréchet derivative, without differentiation in the group coordinates. -/
theorem parameterOperatorDerivative_coefficient
    (D : P → SmoothDifferentialOperator N) (indices : Finset (Fin N → ℕ))
    (hcoeff : ∀ a ∈ indices, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × (Fin N → ℝ) => (D z.1).coefficient a z.2))
    (p v : P) (a : Fin N → ℕ) (ha : a ∈ indices) (u : Fin N → ℝ) :
    (parameterOperatorDerivative D indices hcoeff p v).coefficient a u =
      fderiv ℝ (fun p' => (D p').coefficient a u) p v := by
  have h := ((hcoeff a ha).differentiable (by simp) (p, u)).hasFDerivAt.comp p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const (𝕜 := ℝ) u p))
  have he := congrArg (fun L : P →L[ℝ] ℝ => L v) h.fderiv
  simpa only [parameterOperatorDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
    Function.comp_def, id_eq] using he.symm

/-- Parameter differentiation preserves the
homogeneous degree of every operator in a smooth fixed-index family.
This discharges BB Rem 11.9 using the coefficient characterization. -/
theorem parameterOperatorDerivative_homogeneous
    (G : HomogeneousGroup N) (D : P → SmoothDifferentialOperator N)
    (indices : Finset (Fin N → ℕ)) (hindices : ∀ p, (D p).indices = indices)
    (hcoeff : ∀ a ∈ indices, ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × (Fin N → ℝ) => (D z.1).coefficient a z.2))
    (β : ℝ) (hD : ∀ p, (D p).IsHomogeneous G β) (p v : P) :
    (parameterOperatorDerivative D indices hcoeff p v).IsHomogeneous G β := by
  apply (G2.operator_homogeneous_iff_coefficients G _ β).mpr
  intro a ha t ht u
  change a ∈ indices at ha
  rw [parameterOperatorDerivative_coefficient D indices hcoeff p v a ha,
    parameterOperatorDerivative_coefficient D indices hcoeff p v a ha]
  have he : (fun p' => (D p').coefficient a (G.dilate t u)) =
      fun p' => t ^ ((∑ j, G.weight j * a j : ℕ) - β) * (D p').coefficient a u := by
    funext p'
    exact (G2.operator_homogeneous_iff_coefficients G (D p') β).mp (hD p') a
      (by rw [hindices]; exact ha) t ht u
  have hd : DifferentiableAt ℝ (fun p' => (D p').coefficient a u) p :=
    ((hcoeff a ha).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p
  rw [he, fderiv_const_mul hd]
  rfl

end RothschildStein.P1
