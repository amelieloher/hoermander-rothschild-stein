-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.G2.PolynomialCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- A smooth homogeneous model multiplier lowers the differential
operator degree by its weight, retaining both endpoint cutoffs and the pole
(BB Lemma 11.23, pp. 554–555; Theorem 11.24, pp. 555–558). -/
def PrincipalTerm.multiplyHomogeneousModel (t : PrincipalTerm F)
    (g : (Fin N → ℝ) → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (d : ℤ)
    (hd : ∀ r : ℝ, 0 < r → ∀ u, g (F.G.dilate r u) = r ^ (d : ℝ) * g u) :
    PrincipalTerm F where
  a := t.a
  b := t.b
  D ξ η := {
    indices := t.indices
    coefficient := fun α u => g u * (t.D ξ η).coefficient α u
    smooth_coefficient := by
      intro α hα
      exact hg.mul ((t.D ξ η).smooth_coefficient α (by rw [t.indices_eq]; exact hα)) }
  indices := t.indices
  indices_eq _ _ := rfl
  coefficient_smooth := by
    intro α hα
    exact (hg.comp contDiff_snd.snd).mul (t.coefficient_smooth α hα)
  degree := t.degree - d
  homogeneous := by
    intro ξ η
    apply (G2.operator_homogeneous_iff_coefficients F.G _ _).mpr
    intro α hα r hr u
    change α ∈ t.indices at hα
    change g (F.G.dilate r u) * (t.D ξ η).coefficient α (F.G.dilate r u) = _
    rw [hd r hr u, t.coefficient_homogeneous α hα ξ η r hr u]
    change _ = r ^ (((∑ j, F.G.weight j * α j : ℕ) : ℝ) -
      ((t.degree - d : ℤ) : ℝ)) * (g u * (t.D ξ η).coefficient α u)
    calc
      _ = (r ^ (d : ℝ) *
          r ^ (((∑ j, F.G.weight j * α j : ℕ) : ℝ) - (t.degree : ℝ))) *
          (g u * (t.D ξ η).coefficient α u) := by ring
      _ = _ := by
        congr 1
        rw [← Real.rpow_add hr]
        congr 1
        simp only [Int.cast_sub]
        ring
  star := t.star

/-- The constructed principal term is precisely the homogeneous
model coefficient times the original kernel (BB (11.37)–(11.38)). -/
theorem PrincipalTerm.multiplyHomogeneousModel_kernel (t : PrincipalTerm F)
    (g : (Fin N → ℝ) → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (d : ℤ)
    (hd : ∀ r : ℝ, 0 < r → ∀ u, g (F.G.dilate r u) = r ^ (d : ℝ) * g u)
    (ξ η : Fin N → ℝ) :
    (t.multiplyHomogeneousModel g hg d hd).kernel ξ η = g (F.Θ η ξ) * t.kernel ξ η := by
  simp only [PrincipalTerm.kernel, SmoothDifferentialOperator.apply,
    PrincipalTerm.multiplyHomogeneousModel, t.indices_eq]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

end RothschildStein.P1
