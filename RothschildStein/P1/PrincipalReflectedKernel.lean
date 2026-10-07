-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalCutoffKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RothschildStein.P1.PrincipalTerm

variable {N : ℕ} {F : KernelFrame N}

/-- Reflection of the model coordinate and exchange of endpoints
preserve the actual principal family's weighted bounds. No evenness of
either selected pole is needed. -/
theorem reflectedCutoffModelKernel_hasWeightedBounds
    (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    HasWeightedBounds F.G (2 - (F.G.homogeneousDimension : ℤ) - t.degree)
      (fun ξ η u => t.cutoffModelKernel η ξ (-u)) := by
  let Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
    fun ξ η u => t.cutoffModelKernel η ξ (-u)
  have hreg : ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry Ψ) {z | z.2.2 ≠ 0} := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) =>
          (z.2.1, z.1, -z.2.2)) :=
      contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.neg)
    exact (t.cutoffModelKernel_contDiffOn hΓ).comp hmap.contDiffOn
      (fun z hz => neg_ne_zero.mpr hz)
  apply hasWeightedBounds_of_homogeneous (hreg.of_le (by simp))
  intro a b r hr u hu
  change t.cutoffModelKernel b a (-F.G.dilate r u) = _
  rw [← kdilate_neg]
  have he : (((2 : ℤ) - F.G.homogeneousDimension - t.degree : ℤ) : ℝ) =
      (2 : ℝ) - F.G.homogeneousDimension - t.degree := by push_cast; rfl
  simpa only [Ψ, ← he, Real.rpow_intCast] using
    t.cutoffModelKernel_homogeneous hΓ hhom b a r hr (-u) (neg_ne_zero.mpr hu)

end RothschildStein.P1.PrincipalTerm
