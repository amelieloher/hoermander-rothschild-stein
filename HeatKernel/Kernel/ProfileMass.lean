-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TranslationKernel
public import RothschildStein.G2.DilationMeasure

/-! # Row mass from translation and dilation identities

Haar invariance makes kernel row mass independent of its center. The exact
parabolic scaling law makes the identity-centered mass invariant under time scaling.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein RothschildStein.G2

/-- Translation commutation identifies every row integral with the identity-centered profile integral. -/
theorem integral_heatRepresentativeKernel_row_eq_profile {n : ℕ} (G : HomogeneousGroup n)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hcomm : ∀ s, 0 < s → ∀ a f,
      T s (leftTranslationL2 G a f) = leftTranslationL2 G a (T s f))
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    (∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) =
      ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t 0 y := by
  simp_rw [heatRepresentativeKernel_eq_profile G T u hu hae hcomm ht x]
  exact integral_leftTranslation G (G.inv x)
    (fun y => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t 0 y)

/-- The exact kernel scaling law makes the profile integral invariant under parabolic time scaling. -/
theorem integral_kernel_profile_parabolic_scaling {n : ℕ} (G : HomogeneousGroup n)
    (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hscale : ∀ r t, 0 < r → 0 < t → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    (∫ y, p (r ^ 2 * t) 0 y) = ∫ y, p t 0 y := by
  have hpoint (y : Fin n → ℝ) : p (r ^ 2 * t) 0 (G.dilate r y) =
      (r ^ G.homogeneousDimension)⁻¹ * p t 0 y := by
    simpa only [dilate_zero] using hscale r t hr ht 0 y
  have hd := integral_dilate G hr (fun y => p (r ^ 2 * t) 0 y)
  have heq : (∫ y, p (r ^ 2 * t) 0 (G.dilate r y)) =
      (r ^ G.homogeneousDimension)⁻¹ * ∫ y, p t 0 y := by
    simp_rw [hpoint]
    exact integral_const_mul _ _
  have hc : (r ^ G.homogeneousDimension)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hr.ne')
  apply mul_left_cancel₀ hc
  have hd' : (r ^ G.homogeneousDimension)⁻¹ * (∫ y, p (r ^ 2 * t) 0 y) =
      ∫ y, p (r ^ 2 * t) 0 (G.dilate r y) := by
    simpa only [smul_eq_mul] using hd.symm
  exact hd'.trans heq

end HeatKernel
