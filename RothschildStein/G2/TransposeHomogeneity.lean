-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.TransposeInvariance
public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Dilation as a homeomorphism, with the reciprocal dilation as inverse. -/
def dilationHomeomorph (t : ℝ) (ht : 0 < t) : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) where
  toFun := G.dilate t
  invFun := G.dilate t⁻¹
  left_inv x := by rw [dilate_dilate G, inv_mul_cancel₀ ht.ne', dilate_one G]
  right_inv x := by rw [dilate_dilate G, mul_inv_cancel₀ ht.ne', dilate_one G]
  continuous_toFun := (contDiff_dilate G t).continuous
  continuous_invFun := (contDiff_dilate G t⁻¹).continuous

/-- The dilation homeomorphism has the dilation as its underlying map. -/
theorem dilationHomeomorph_apply (t : ℝ) (ht : 0 < t) (x : Fin N → ℝ) :
    dilationHomeomorph G t ht x = G.dilate t x := rfl

private theorem transpose_scales_homeomorph
    (T : (Fin N → ℝ) ≃ₜ (Fin N → ℝ))
    (hsT : ContDiff ℝ (⊤ : ℕ∞) T) (hsI : ContDiff ℝ (⊤ : ℕ∞) T.symm)
    (J c : ℝ) (hi : ∀ h : (Fin N → ℝ) → ℝ, ∫ x, h (T x) = J * ∫ x, h x)
    {P Q : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ}
    (ht : TransposeRelation P Q) (hQs : PreservesSmooth Q)
    (hP : ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → ∀ x, P (f ∘ T) x = c * P f (T x))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Q (f ∘ T) = fun x => c * Q f (T x) := by
  apply continuous_eq_of_test_pairings (hQs _ (hf.comp hsT)).continuous
    (continuous_const.mul ((hQs _ hf).continuous.comp hsT.continuous))
  intro g hg hcg
  have hg' := hg.comp hsI
  have hcg' := hcg.comp_homeomorph T.symm
  have he : (g ∘ T.symm) ∘ T = g := by funext x; simp
  have hPi : ∀ x, P g (T.symm x) = c * P (g ∘ T.symm) x := by
    intro x
    have h := hP (g ∘ T.symm) hg' (T.symm x)
    rw [he, T.apply_symm_apply] at h
    exact h
  calc
    (∫ x, g x * Q (f ∘ T) x) = ∫ x, P g x * f (T x) :=
      (ht g hg (f ∘ T) (hf.comp hsT) (Or.inl hcg)).symm
    _ = J * ∫ x, P g (T.symm x) * f x := by
      simpa only [T.symm_apply_apply] using hi (fun x => P g (T.symm x) * f x)
    _ = J * (c * ∫ x, P (g ∘ T.symm) x * f x) := by
      simp_rw [hPi, _root_.mul_assoc]
      rw [integral_const_mul]
    _ = J * (c * ∫ x, g (T.symm x) * Q f x) := by
      rw [ht _ hg' f hf (Or.inl hcg')]
      rfl
    _ = c * ∫ x, g x * Q f (T x) := by
      have h := hi (fun x => g (T.symm x) * Q f x)
      simp only [T.symm_apply_apply] at h
      rw [h]
      ring
    _ = ∫ x, g x * (c * Q f (T x)) := by
      rw [show (fun x => g x * (c * Q f (T x))) =
        (fun x => c * (g x * Q f (T x))) by funext x; ring, integral_const_mul]

/-- Transposition preserves homogeneity degree, using the exact transpose identity
(BB Proposition 3.24(b), p. 108). -/
theorem transpose_homogeneous_of_relation
    {P Q : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ} {β : ℝ}
    (ht : TransposeRelation P Q) (hQs : PreservesSmooth Q)
    (hP : IsHomogeneousOperator G P β) : IsHomogeneousOperator G Q β := by
  intro f hf t htpos x
  exact congrFun (transpose_scales_homeomorph (dilationHomeomorph G t htpos)
    (contDiff_dilate G t) (contDiff_dilate G t⁻¹)
    ((t ^ G.homogeneousDimension)⁻¹) (t ^ β)
    (by intro h; simpa only [dilationHomeomorph_apply, smul_eq_mul] using integral_dilate G htpos h)
    ht hQs (fun g hg x => hP g hg t htpos x) f hf) x

end RothschildStein.G2
