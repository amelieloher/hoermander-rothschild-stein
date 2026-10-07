-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace RothschildStein.G2
variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)

/-- A nonzero convolution value lies in the group product
of the two supports (BB Def 3.44, pp. 118–119; support). -/
theorem support_groupConvolution_subset (f g : (Fin N → ℝ) → 𝕜) :
    support (groupConvolution G f g) ⊆
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 p.2) ''
        (support f ×ˢ support g) := by
  intro x hx
  by_contra hn
  have hz : ∀ y, f y * g (G.mul (G.inv y) x) = 0 := by
    intro y
    by_cases hf : f y = 0
    · simp only [hf, MulZeroClass.zero_mul]
    have hg : g (G.mul (G.inv y) x) = 0 := by
      by_contra hg
      apply hn
      refine ⟨(y, G.mul (G.inv y) x), ⟨hf, hg⟩, ?_⟩
      simp only [← mul_assoc G, mul_inv, zero_mul]
    simp only [hg, MulZeroClass.mul_zero]
  apply hx
  rw [groupConvolution_eq_integral]
  simp only [hz, integral_zero]

/-- Compact supports give a compact support for convolution,
without requiring the Bochner integral to exist (BB p. 119; support). -/
theorem hasCompactSupport_groupConvolution {f g : (Fin N → ℝ) → 𝕜}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (groupConvolution G f g) := by
  have hc := (hf.isCompact.prod hg.isCompact).image (continuous_mul G)
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  exact (support_groupConvolution_subset G f g).trans
    (image_mono (prod_mono subset_closure subset_closure))

/-- Additivity in the second slot at points where both integrals
converge absolutely (BB p. 119; bilinearity). -/
theorem groupConvolution_add_right (f g₁ g₂ : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ)
    (h₁ : GroupConvolutionExistsAt G f g₁ x)
    (h₂ : GroupConvolutionExistsAt G f g₂ x) :
    groupConvolution G f (g₁ + g₂) x =
      groupConvolution G f g₁ x + groupConvolution G f g₂ x := by
  simp only [groupConvolution_eq_integral, Pi.add_apply, mul_add]
  exact integral_add h₁ h₂

/-- Scalar multiplication in the second slot (BB p. 119). -/
theorem groupConvolution_smul_right (c : 𝕜) (f g : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ) :
    groupConvolution G f (c • g) x = c * groupConvolution G f g x := by
  simp only [groupConvolution_eq_integral, Pi.smul_apply, smul_eq_mul,
    mul_left_comm (f _ ) c]
  exact integral_const_mul c _

end RothschildStein.G2
