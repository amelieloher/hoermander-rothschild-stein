-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.TwoSidedInverse
public import RothschildStein.H1.FundamentalUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Inversion preserves local integrability of the fundamental
kernel (BB Theorem 6.20(4), p. 271). -/
theorem locallyIntegrable_comp_inv {f : (Fin N → ℝ) → ℝ} (hf : LocallyIntegrable f) :
    LocallyIntegrable (fun x => f (G.inv x)) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := hf.integrableOn_isCompact (hK.image (G2.continuous_inv G))
  have hm : IntegrableOn f (G.inv '' K) (volume.map G.inv) := by
    rw [(G2.measurePreserving_inv G).map_eq]
    exact hi
  have he : MeasurableEmbedding G.inv :=
    (G2.continuous_inv G).measurable.measurableEmbedding (G2.inv_bijective G).injective
  exact (he.integrableOn_map_iff.mp hm).mono_set (subset_preimage_image G.inv K)

/-- Reflection preserves punctured smoothness, without any
assumption that inversion is coordinate negation (BB p. 271). -/
theorem contDiffOn_comp_inv_off_zero {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : Fin N → ℝ)}ᶜ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (G.inv x)) ({(0 : Fin N → ℝ)}ᶜ) := by
  apply hf.comp (G2.contDiff_inv G).contDiffOn
  intro x hx hz
  change x ≠ 0 at hx
  change G.inv x = 0 at hz
  apply hx
  have he := congrArg G.inv hz
  simpa only [G2.inv_inv, G2.inv_zero] using he

/-- Reflection preserves the punctured scalar homogeneity
(BB p. 271). -/
theorem homogeneous_comp_inv {a : ℝ} {f : (Fin N → ℝ) → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x) :
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.inv (G.dilate t x)) = t ^ a * f (G.inv x) := by
  intro t ht x hx
  rw [G2.inv_dilate G ht]
  apply hf t ht
  intro hz
  have he := congrArg G.inv hz
  apply hx
  simpa only [G2.inv_inv, G2.inv_zero] using he

/-- The transpose of the reversed-drift system is the original
operator on every compact smooth test (BB p. 271). -/
theorem StandingHypotheses.reverseDrift_transpose_operator
    (H : StandingHypotheses G q) {φ : (Fin N → ℝ) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin N → ℝ) :
    sumSquaresWithDriftTranspose (H.reverseDrift G).fields φ x =
      sumSquaresWithDrift H.fields φ x := by
  rw [(H.reverseDrift G).sumSquaresTranspose_formula G φ hφ]
  simp_rw [H.reverseDrift_horizontal G]
  change -(fderiv ℝ φ x ((H.reverseDrift G).fields 0 x)) + _ = _
  have h0 : (H.reverseDrift G).fields 0 x = -(H.fields 0 x) := by
    simp [StandingHypotheses.reverseDrift, driftSign]
  rw [h0, map_neg, neg_neg]
  rfl

/-- The reflected kernel is a fundamental kernel for the
reversed-drift operator, by the proved two-sided identity at zero
(BB Theorem 6.20(4), printed p. 271). -/
theorem StandingHypotheses.reflected_fundamental_pairing
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hcΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hhΓ : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (hfund : ∀ ψ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ y, Γ y * sumSquaresWithDriftTranspose H.fields ψ y) = ψ 0)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ y, Γ (G.inv y) * sumSquaresWithDriftTranspose (H.reverseDrift G).fields φ y) = φ 0 := by
  have h := H.fundamental_twoSidedInverse G hQ hΓ hcΓ hhΓ hfund hφ hcφ 0
  simp only [G2.mul_zero] at h
  simpa only [H.reverseDrift_transpose_operator G hφ] using h

end RothschildStein.H1
