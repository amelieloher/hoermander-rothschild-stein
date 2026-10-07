-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorConsequences

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RothschildStein.P1

/-- Acting on a globally smooth homogeneous
coefficient subtracts the homogeneous field degree, including at zero.
The proof reuses the established operator covariance (BB Proposition
3.23, p. 107; Lemma 11.18, p. 549). -/
theorem fieldDerivative_global_homogeneous {N : ℕ} (G : HomogeneousGroup N)
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k β : ℝ}
    (hV : G2.IsHomogeneousField G V k)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (G.dilate t x) = t ^ β * f x)
    {t : ℝ} (ht : 0 < t) (x : Fin N → ℝ) :
    fieldDerivative V f (G.dilate t x) = t ^ (β - k) * fieldDerivative V f x := by
  have hop := (G2.isHomogeneousField_iff_operator G V k).mp hV f hf t ht x
  have he : f ∘ G.dilate t = fun y => t ^ β * f y := by
    funext y
    exact hhom t ht y
  have hscale : fieldDerivative V (f ∘ G.dilate t) x = t ^ β * fieldDerivative V f x := by
    unfold fieldDerivative
    rw [he]
    change fderiv ℝ ((t ^ β) • f) x (V x) = _
    rw [fderiv_const_smul_field]
    rfl
  rw [hscale] at hop
  apply mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht k))
  rw [← mul_assoc, ← Real.rpow_add ht]
  have hk : k + (β - k) = β := by ring
  rw [hk]
  exact hop.symm

/-- A coordinate derivative of a smooth
homogeneous coefficient has degree β−weight(j) at every point.
This supplies the differentiated-coefficient terms in the actual
finite leading operator (BB Lemma 11.18, p. 549). -/
theorem coordinatePartial_global_homogeneous {N : ℕ} (G : HomogeneousGroup N)
    (j : Fin N) {β : ℝ} {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (G.dilate t x) = t ^ β * f x)
    {t : ℝ} (ht : 0 < t) (x : Fin N → ℝ) :
    fderiv ℝ f (G.dilate t x) (Pi.single j 1) =
      t ^ (β - G.weight j) * fderiv ℝ f x (Pi.single j 1) := by
  have hV := (G2.isHomogeneousField_iff_operator G
    (fun _ => Hormander.Interface.basisVec j) (G.weight j)).mpr
      (G2.coordinateDerivative_homogeneous G j)
  simpa only [fieldDerivative, Hormander.Interface.basisVec] using
    fieldDerivative_global_homogeneous G hV hf hhom ht x

end RothschildStein.P1
