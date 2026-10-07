-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TaylorWordMonomial
public import RothschildStein.P1.TypeKernel
public import RothschildStein.G2.OperatorCoefficientCriterion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1

/-- The effective single-index differential
operator attached to one coordinate Taylor monomial. -/
def taylorMonomialPartial {N : ℕ} (α : Fin N → ℕ) (J : List (Fin N))
    (c : ℝ) : SmoothDifferentialOperator N where
  indices := {α}
  coefficient _ u := c * taylorWordMonomial J u
  smooth_coefficient _ _ := contDiff_const.mul (taylorWordMonomial_contDiff J)

/-- A Taylor monomial operator acts by exactly
that monomial times the selected coordinate partial. -/
theorem taylorMonomialPartial_apply {N : ℕ} (α : Fin N → ℕ) (J : List (Fin N))
    (c : ℝ) (g : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    (taylorMonomialPartial α J c).apply g u =
      c * taylorWordMonomial J u * euclideanPartial α g u := by
  classical
  simp only [SmoothDifferentialOperator.apply, taylorMonomialPartial, Finset.sum_singleton]

/-- The exact differential degree subtracts the
Taylor monomial weight from the derivative multi-index weight. -/
theorem taylorMonomialPartial_homogeneous {N : ℕ} (G : HomogeneousGroup N)
    (α : Fin N → ℕ) (J : List (Fin N)) (c : ℝ) :
    (taylorMonomialPartial α J c).IsHomogeneous G
      (((((∑ j, G.weight j * α j : ℕ) : ℤ) - ((J.map G.weight).sum : ℤ)) : ℤ) : ℝ) := by
  classical
  let degree : ℤ := ((∑ j, G.weight j * α j : ℕ) : ℤ) - ((J.map G.weight).sum : ℤ)
  apply (G2.operator_homogeneous_iff_coefficients G _ _).mpr
  intro β hβ r hr u
  have hβα : β = α := Finset.mem_singleton.mp hβ
  subst β
  change c * taylorWordMonomial J (G.dilate r u) =
    r ^ (((∑ j, G.weight j * α j : ℕ) : ℝ) - (degree : ℝ)) *
        (c * taylorWordMonomial J u)
  have he : ((∑ j, G.weight j * α j : ℕ) : ℝ) - (degree : ℝ) =
      ((J.map G.weight).sum : ℝ) := by
    dsimp only [degree]
    simp only [Int.cast_sub, Int.cast_natCast]
    ring
  rw [taylorWordMonomial_homogeneous, he, Real.rpow_natCast]
  ring

/-- A smooth parameter coefficient times one
Taylor monomial and one pole partial is a principal term `PrincipalTerm`. -/
def PrincipalTerm.ofTaylorWord {N : ℕ} (F : KernelFrame N)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) (α : Fin N → ℕ) (J : List (Fin N))
    (c : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (star : Bool) : PrincipalTerm F where
  a := a
  b := b
  D ξ η := taylorMonomialPartial α J (c (ξ, η))
  indices := {α}
  indices_eq _ _ := rfl
  coefficient_smooth := by
    intro _ _
    exact (hc.comp (contDiff_fst.prodMk contDiff_snd.fst)).mul
      ((taylorWordMonomial_contDiff J).comp contDiff_snd.snd)
  degree := ((∑ j, F.G.weight j * α j : ℕ) : ℤ) - ((J.map F.G.weight).sum : ℤ)
  homogeneous ξ η := taylorMonomialPartial_homogeneous F.G α J (c (ξ, η))
  star := star

/-- The assembled principal term has precisely
the cutoff Taylor-monomial kernel, with its original pole choice. -/
theorem PrincipalTerm.ofTaylorWord_kernel {N : ℕ} (F : KernelFrame N)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) (α : Fin N → ℕ) (J : List (Fin N))
    (c : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (star : Bool) (ξ η : Fin N → ℝ) :
    (PrincipalTerm.ofTaylorWord F a b α J c hc star).kernel ξ η =
      a ξ * b η * (taylorWordMonomial J (F.Θ η ξ) * c (ξ, η) *
        euclideanPartial α (F.pole star) (F.Θ η ξ)) := by
  change a ξ * b η * (taylorMonomialPartial α J (c (ξ, η))).apply (F.pole star) (F.Θ η ξ) = _
  rw [taylorMonomialPartial_apply]
  ring

end RothschildStein.P1
