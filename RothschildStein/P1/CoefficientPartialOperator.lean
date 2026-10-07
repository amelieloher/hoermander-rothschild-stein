-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorCoefficientCriterion
public import RothschildStein.P1.TypeKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1

/-- One actual finite differential term with
an arbitrary smooth coefficient, used for differentiated principal terms. -/
def coefficientPartial {N : ℕ} (α : Fin N → ℕ) (c : (Fin N → ℝ) → ℝ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) : SmoothDifferentialOperator N where
  indices := {α}
  coefficient := fun _ => c
  smooth_coefficient := fun _ _ => hc

/-- The one-term operator acts by its actual
coefficient times the multi-index derivative `euclideanPartial`. -/
theorem coefficientPartial_apply {N : ℕ} (α : Fin N → ℕ)
    (c : (Fin N → ℝ) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (g : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    (coefficientPartial α c hc).apply g u = c u * euclideanPartial α g u := by
  simp only [SmoothDifferentialOperator.apply, coefficientPartial, Finset.sum_singleton]

/-- The one-term operator has the precise
degree given by the established coefficient homogeneity criterion
(BB Proposition 3.23, p. 107; Lemma 11.18, p. 549). -/
theorem coefficientPartial_homogeneous {N : ℕ} (G : HomogeneousGroup N)
    (α : Fin N → ℕ) (c : (Fin N → ℝ) → ℝ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (d : ℝ)
    (hh : ∀ r : ℝ, 0 < r → ∀ u,
      c (G.dilate r u) = r ^ ((∑ j, G.weight j * α j : ℕ) - d) * c u) :
    (coefficientPartial α c hc).IsHomogeneous G d := by
  apply (G2.operator_homogeneous_iff_coefficients G _ d).mpr
  intro β hβ r hr u
  have he : β = α := Finset.mem_singleton.mp hβ
  subst β
  exact hh r hr u

/-- A jointly smooth homogeneous coefficient
family gives an actual principal term, retaining both endpoint cutoffs
and the selected pole. -/
def PrincipalTerm.ofCoefficientPartial {N : ℕ} (F : KernelFrame N)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) (α : Fin N → ℕ)
    (A : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (d : ℤ)
    (hh : ∀ ξ η, ∀ r : ℝ, 0 < r → ∀ u,
      A (ξ, η, F.G.dilate r u) =
        r ^ ((∑ j, F.G.weight j * α j : ℕ) - (d : ℝ)) * A (ξ, η, u))
    (star : Bool) : PrincipalTerm F where
  a := a
  b := b
  D := fun ξ η => coefficientPartial α (fun u => A (ξ, η, u))
    (hA.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))
  indices := {α}
  indices_eq := fun _ _ => rfl
  coefficient_smooth := fun _ _ => hA
  degree := d
  homogeneous := fun ξ η => coefficientPartial_homogeneous F.G α _ _ d (hh ξ η)
  star := star

/-- The constructed principal term has
exactly the coefficient-times-pole-partial kernel required by the
finite Leibniz expansion. -/
theorem PrincipalTerm.ofCoefficientPartial_kernel {N : ℕ} (F : KernelFrame N)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) (α : Fin N → ℕ)
    (A : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (d : ℤ)
    (hh : ∀ ξ η, ∀ r : ℝ, 0 < r → ∀ u,
      A (ξ, η, F.G.dilate r u) =
        r ^ ((∑ j, F.G.weight j * α j : ℕ) - (d : ℝ)) * A (ξ, η, u))
    (star : Bool) (ξ η : Fin N → ℝ) :
    (PrincipalTerm.ofCoefficientPartial F a b α A hA d hh star).kernel ξ η =
      a ξ * b η * (A (ξ, η, F.Θ η ξ) * euclideanPartial α (F.pole star) (F.Θ η ξ)) := by
  simp only [PrincipalTerm.kernel, PrincipalTerm.ofCoefficientPartial, coefficientPartial_apply]

end RothschildStein.P1
