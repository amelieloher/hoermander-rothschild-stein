-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import RothschildStein.P1.KernelEstimatesHomogeneous
public import RothschildStein.H1.PuncturedOperatorHomogeneity
public import RothschildStein.H1.LocalFinitePartialPairing

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators

namespace RothschildStein.P1.PrincipalTerm

variable {N : ℕ} {F : KernelFrame N}

/-- The actual differential operator applied to its selected pole,
before composition with the chart and endpoint cutoffs. -/
def modelKernel (t : PrincipalTerm F) (ξ η u : Fin N → ℝ) : ℝ :=
  (t.D ξ η).apply (F.pole t.star) u

/-- Joint smoothness of the actual parametrized principal model kernel
off the pole follows from joint coefficient smoothness and punctured pole smoothness. -/
theorem modelKernel_contDiffOn (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry t.modelKernel)
      {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} := by
  have hpartial (a : Fin N → ℕ) : ContDiffOn ℝ (⊤ : ℕ∞)
      (euclideanPartial a (F.pole t.star)) {(0 : Fin N → ℝ)}ᶜ := by
    apply contDiffOn_iff_forall_nat_le.mpr
    intro m _
    exact H1.contDiffOn_euclideanPartial_finite
      ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩ a m (F.pole t.star)
      (hΓ.of_le (by simp))
  have he : kernelUncurry t.modelKernel =
      fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) =>
        ∑ a ∈ t.indices, (t.D z.1 z.2.1).coefficient a z.2.2 *
          euclideanPartial a (F.pole t.star) z.2.2 := by
    funext z
    simp only [kernelUncurry, modelKernel, SmoothDifferentialOperator.apply, t.indices_eq]
  rw [he]
  apply ContDiffOn.sum
  intro a ha
  apply (t.coefficient_smooth a ha).contDiffOn.mul
  exact (hpartial a).comp contDiff_snd.snd.contDiffOn (fun z hz => by simpa using hz)

/-- Applying the actual homogeneous operator subtracts its degree
from the fundamental kernel degree, despite the singularity at zero. -/
theorem modelKernel_homogeneous (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    ∀ ξ η : Fin N → ℝ, ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      t.modelKernel ξ η (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension - t.degree) * t.modelKernel ξ η u := by
  intro ξ η r hr u hu
  exact H1.differentialOperator_punctured_homogeneity F.G (t.D ξ η)
    (t.homogeneous ξ η) hΓ hhom hr hu

end RothschildStein.P1.PrincipalTerm
