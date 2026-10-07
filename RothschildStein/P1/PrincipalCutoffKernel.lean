-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalModelKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace RothschildStein.P1.PrincipalTerm

variable {N : ℕ} {F : KernelFrame N}

/-- The full principal family, with both endpoint cutoffs and the
actual homogeneous differential operator applied to its selected pole. -/
def cutoffModelKernel (t : PrincipalTerm F) (ξ η u : Fin N → ℝ) : ℝ :=
  t.a ξ * t.b η * t.modelKernel ξ η u

/-- Composition of the full principal family with the chart is the
cut-off model kernel `cutoffModelKernel`. -/
theorem kernel_eq_cutoffModelKernel (t : PrincipalTerm F) (ξ η : Fin N → ℝ) :
    t.kernel ξ η = t.cutoffModelKernel ξ η (F.Θ η ξ) := rfl

/-- Endpoint cutoffs preserve joint smoothness off the pole. -/
theorem cutoffModelKernel_contDiffOn (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry t.cutoffModelKernel)
      {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} := by
  exact ((t.a.contDiff.comp contDiff_fst).contDiffOn.mul
    (t.b.contDiff.comp contDiff_snd.fst).contDiffOn).mul (t.modelKernel_contDiffOn hΓ)

/-- Endpoint cutoffs preserve the actual homogeneous degree of the
principal family. -/
theorem cutoffModelKernel_homogeneous (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    ∀ ξ η : Fin N → ℝ, ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      t.cutoffModelKernel ξ η (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension - t.degree) * t.cutoffModelKernel ξ η u := by
  intro ξ η r hr u hu
  simp only [cutoffModelKernel, t.modelKernel_homogeneous hΓ hhom ξ η r hr u hu]
  ring

/-- The full principal family satisfies the uniform model bounds,
including parameter derivatives that differentiate the cutoffs. -/
theorem cutoffModelKernel_hasWeightedBounds (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    HasWeightedBounds F.G (2 - (F.G.homogeneousDimension : ℤ) - t.degree) t.cutoffModelKernel := by
  apply hasWeightedBounds_of_homogeneous (t.cutoffModelKernel_contDiffOn hΓ |>.of_le (by simp))
  intro ξ η r hr u hu
  have he : (((2 : ℤ) - F.G.homogeneousDimension - t.degree : ℤ) : ℝ) =
      (2 : ℝ) - F.G.homogeneousDimension - t.degree := by push_cast; rfl
  simpa only [← he, Real.rpow_intCast] using
    t.cutoffModelKernel_homogeneous hΓ hhom ξ η r hr u hu

end RothschildStein.P1.PrincipalTerm
