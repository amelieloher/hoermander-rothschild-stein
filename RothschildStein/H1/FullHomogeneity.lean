-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ScaledDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Full positive-scale homogeneity follows from the local fundamental-kernel assumptions. Local weak regularity applies to the scaled defect, and negative dyadic rigidity then gives the claim (BB p. 266). -/
theorem StandingHypotheses.fundamental_fullHomogeneity
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hdyadic : ∀ x, x ≠ 0 → Γ (G.dilate 2 x) =
      (2 : ℝ) ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (hfund : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0)
    {t : ℝ} (ht : 0 < t) (x : Fin N → ℝ) (hx : x ≠ 0) :
    Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x := by
  have h := H.scaledFundamentalKernel_eq G hQ hΓ hc hdyadic hfund (inv_pos.mpr ht) x hx
  rw [scaledFundamentalKernel_eq_rpow G (inv_pos.mpr ht), inv_inv, Real.inv_rpow ht.le] at h
  have hn : t ^ (2 - (G.homogeneousDimension : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have Ht := congrArg (fun r : ℝ => t ^ (2 - (G.homogeneousDimension : ℝ)) * r) h
  change t ^ (2 - (G.homogeneousDimension : ℝ)) *
    ((t ^ (2 - (G.homogeneousDimension : ℝ)))⁻¹ * Γ (G.dilate t x)) = _ at Ht
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul] at Ht
  exact Ht

/-- The function homogeneity gives the exact distributional
pairing exponent -2, with no assertion about the arbitrary value at zero
(BB Definition 6.16, p. 264). -/
theorem fundamental_distributionHomogeneity
    {Γ : (Fin N → ℝ) → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    {t : ℝ} (ht : 0 < t) (φ : (Fin N → ℝ) → ℝ) :
    (∫ x, Γ x * φ (G.dilate t x)) = t ^ (-2 : ℝ) * ∫ x, Γ x * φ x := by
  let : NeZero N := ⟨Nat.ne_of_gt G.dimension_pos⟩
  have hd := G2.integral_dilate G ht (fun y => Γ (G.dilate t⁻¹ y) * φ y)
  simp only [G2.dilate_inv_dilate G ht.ne', smul_eq_mul] at hd
  have he : (fun y => Γ (G.dilate t⁻¹ y) * φ y) =ᵐ[volume]
      (fun y => t⁻¹ ^ (2 - (G.homogeneousDimension : ℝ)) * (Γ y * φ y)) := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with y hy
    rw [hhom t⁻¹ (inv_pos.mpr ht) y hy, mul_assoc]
  rw [integral_congr_ae he, integral_const_mul] at hd
  have hfactor : (t ^ G.homogeneousDimension)⁻¹ *
      t⁻¹ ^ (2 - (G.homogeneousDimension : ℝ)) = t ^ (-2 : ℝ) := by
    rw [Real.inv_rpow ht.le, Real.rpow_sub ht, Real.rpow_natCast, Real.rpow_two,
      Real.rpow_neg ht.le, Real.rpow_two]
    field_simp [ht.ne']
  rw [← mul_assoc, hfactor] at hd
  exact hd

end RothschildStein.H1
