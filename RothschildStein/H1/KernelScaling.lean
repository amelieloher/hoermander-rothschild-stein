-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.DilationMeasure
public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Fundamental-solution scaling, in the equivalent integer-power
normalization s²/s^Q (BB (6.22)–(6.26), p. 265). -/
def scaledFundamentalKernel (s : ℝ) (Γ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  (s ^ 2 * (s ^ G.homogeneousDimension)⁻¹) * Γ (G.dilate s⁻¹ x)

/-- Error-kernel scaling s^{-Q} (BB (6.22)–(6.26), p. 265). -/
def scaledErrorKernel (s : ℝ) (E : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  (s ^ G.homogeneousDimension)⁻¹ * E (G.dilate s⁻¹ x)

/-- The normalization is exactly s^{2-Q} at positive scales (BB p. 265). -/
theorem scaledFundamentalKernel_eq_rpow {s : ℝ} (hs : 0 < s)
    (Γ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    scaledFundamentalKernel G s Γ x =
      s ^ (2 - (G.homogeneousDimension : ℝ)) * Γ (G.dilate s⁻¹ x) := by
  unfold scaledFundamentalKernel
  rw [Real.rpow_sub hs, Real.rpow_natCast, Real.rpow_two]
  rfl

/-- Kernel scalings compose multiplicatively (BB p. 265). -/
theorem scaledFundamentalKernel_comp (s t : ℝ) (Γ : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) :
    scaledFundamentalKernel G s (scaledFundamentalKernel G t Γ) x =
      scaledFundamentalKernel G (s * t) Γ x := by
  simp only [scaledFundamentalKernel, G2.dilate_dilate, mul_pow, mul_inv_rev]
  rw [mul_comm t⁻¹ s⁻¹]
  ring

/-- The correction omega generates the exact consecutive-scale difference, on the same carrier including the origin (BB p. 265). -/
theorem scaledFundamentalKernel_double_sub (s : ℝ) (Γ : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) :
    scaledFundamentalKernel G (2 * s) Γ x - scaledFundamentalKernel G s Γ x =
      scaledFundamentalKernel G s (fun y => scaledFundamentalKernel G 2 Γ y - Γ y) x := by
  have h := scaledFundamentalKernel_comp G s 2 Γ x
  rw [mul_comm s 2] at h
  rw [← h]
  simp only [scaledFundamentalKernel]
  ring

/-- Scaling transfers the weak pairing identity for any degree-two
operator. The right side is the complete unscaled identity, on every compact
smooth test, rather than an assumption about the scaled conclusion (BB p. 265). -/
theorem scaled_pairing_identity
    (P : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ)
    (hP : G2.IsHomogeneousOperator G P 2)
    (Γ E : (Fin N → ℝ) → ℝ)
    (hΓ : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * P φ x) = φ 0 + ∫ x, E x * φ x)
    {s : ℝ} (hs : 0 < s) (φ : (Fin N → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcompact : HasCompactSupport φ) :
    (∫ x, scaledFundamentalKernel G s Γ x * P φ x) =
      φ 0 + ∫ x, scaledErrorKernel G s E x * φ x := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := G.dilate s
      invFun := G.dilate s⁻¹
      left_inv := G2.dilate_inv_dilate G hs.ne'
      right_inv := by intro x; rw [G2.dilate_dilate, mul_inv_cancel₀ hs.ne', G2.dilate_one]
      continuous_toFun := (G2.contDiff_dilate G s).continuous
      continuous_invFun := (G2.contDiff_dilate G s⁻¹).continuous }
  have htest := hΓ (φ ∘ G.dilate s)
    (hφ.comp (G2.contDiff_dilate G s)) (hcompact.comp_homeomorph e)
  have hl : (∫ x, scaledFundamentalKernel G s Γ x * P φ x) =
      ∫ x, Γ x * P (φ ∘ G.dilate s) x := by
    have hd := G2.integral_dilate G (inv_pos.mpr hs)
      (fun y => Γ y * P φ (G.dilate s y))
    simp only [G2.dilate_dilate, mul_inv_cancel₀ hs.ne', G2.dilate_one, smul_eq_mul,
      inv_pow, inv_inv] at hd
    simp only [scaledFundamentalKernel, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hd]
    have he : (fun x => Γ x * P (φ ∘ G.dilate s) x) =
        (fun x => s ^ 2 * (Γ x * P φ (G.dilate s x))) := by
      funext x
      rw [hP φ hφ s hs x, Real.rpow_two]
      ring
    rw [he, integral_const_mul]
    field_simp [hs.ne']
  have hr : (∫ x, scaledErrorKernel G s E x * φ x) = ∫ x, E x * φ (G.dilate s x) := by
    have hd := G2.integral_dilate G (inv_pos.mpr hs)
      (fun y => E y * φ (G.dilate s y))
    simp only [G2.dilate_dilate, mul_inv_cancel₀ hs.ne', G2.dilate_one, smul_eq_mul,
      inv_pow, inv_inv] at hd
    simp only [scaledErrorKernel, mul_assoc]
    rw [integral_const_mul, hd]
    field_simp [hs.ne']
  rw [hl, htest, hr]
  simp only [Function.comp_apply, G2.dilate_zero]

end RothschildStein.H1
