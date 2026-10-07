-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.P1.TaylorWordMonomial

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- A smooth endpoint coefficient and coordinate
Taylor monomial multiply an actual principal operator. The exact operator
degree is reduced by the monomial weight (BB Lemma 11.16, pp. 548–549). -/
def PrincipalTerm.multiplyModelMonomial (t : PrincipalTerm F) (J : List (Fin N))
    (A : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    PrincipalTerm F where
  a := t.a
  b := t.b
  D ξ η := {
    indices := t.indices
    coefficient := fun α u => A (ξ, η) * taylorWordMonomial J u * (t.D ξ η).coefficient α u
    smooth_coefficient := by
      intro α hα
      exact (contDiff_const.mul (taylorWordMonomial_contDiff J)).mul
        ((t.D ξ η).smooth_coefficient α (by rw [t.indices_eq]; exact hα)) }
  indices := t.indices
  indices_eq _ _ := rfl
  coefficient_smooth := by
    intro α hα
    exact ((hA.comp (contDiff_fst.prodMk contDiff_snd.fst)).mul
      ((taylorWordMonomial_contDiff J).comp contDiff_snd.snd)).mul
      (t.coefficient_smooth α hα)
  degree := t.degree - ((J.map F.G.weight).sum : ℤ)
  homogeneous := by
    intro ξ η
    apply (G2.operator_homogeneous_iff_coefficients F.G _ _).mpr
    intro α hα r hr u
    change α ∈ t.indices at hα
    change A (ξ, η) * taylorWordMonomial J (F.G.dilate r u) *
      (t.D ξ η).coefficient α (F.G.dilate r u) = _
    rw [taylorWordMonomial_homogeneous, t.coefficient_homogeneous α hα ξ η r hr u]
    rw [← Real.rpow_natCast]
    change _ = r ^ (((∑ i, F.G.weight i * α i : ℕ) : ℝ) -
      ((t.degree - ((J.map F.G.weight).sum : ℤ) : ℤ) : ℝ)) *
      (A (ξ, η) * taylorWordMonomial J u * (t.D ξ η).coefficient α u)
    calc
      _ = (r ^ ((J.map F.G.weight).sum : ℝ) *
          r ^ (((∑ i, F.G.weight i * α i : ℕ) : ℝ) - (t.degree : ℝ))) *
          (A (ξ, η) * taylorWordMonomial J u * (t.D ξ η).coefficient α u) := by ring
      _ = _ := by
        congr 1
        rw [← Real.rpow_add hr]
        congr 1
        simp only [Int.cast_sub, Int.cast_natCast]
        ring
  star := t.star

/-- The new term is precisely the scalar
Taylor monomial times the original principal kernel. -/
theorem PrincipalTerm.multiplyModelMonomial_kernel (t : PrincipalTerm F) (J : List (Fin N))
    (A : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (ξ η : Fin N → ℝ) :
    (t.multiplyModelMonomial J A hA).kernel ξ η =
      A (ξ, η) * taylorWordMonomial J (F.Θ η ξ) * t.kernel ξ η := by
  classical
  simp only [PrincipalTerm.kernel, SmoothDifferentialOperator.apply,
    PrincipalTerm.multiplyModelMonomial, t.indices_eq]
  have he : (∑ α ∈ t.indices,
      A (ξ, η) * taylorWordMonomial J (F.Θ η ξ) * (t.D ξ η).coefficient α (F.Θ η ξ) *
        euclideanPartial α (F.pole t.star) (F.Θ η ξ)) =
      A (ξ, η) * taylorWordMonomial J (F.Θ η ξ) *
        (∑ α ∈ t.indices, (t.D ξ η).coefficient α (F.Θ η ξ) *
          euclideanPartial α (F.pole t.star) (F.Θ η ξ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [he]
  ring

end RothschildStein.P1
