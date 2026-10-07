-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Standing
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.Definitions.sumSquaresWithDriftTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The field transpose is the negative action (BB p. 111). -/
theorem StandingHypotheses.fieldTranspose_eq_neg (H : StandingHypotheses G q)
    (i : Fin (q + 1)) (φ : (Fin N → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    fieldTranspose (H.fields i) φ = -fieldDerivative (H.fields i) φ := by
  rw [(H.invariant i).eq_leftField G]
  funext x
  exact G2.leftField_transpose G _ φ hφ x

/-- Differentiation by smooth fields preserves smooth scalar functions. -/
theorem smooth_fieldDerivative (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative V f) :=
  (hf.fderiv_right (by simp)).clm_apply hV

/-- The transpose of the square of an invariant field is its square
(BB p. 254; each first-order transpose contributes a negative sign). -/
theorem StandingHypotheses.squareTranspose (H : StandingHypotheses G q)
    (i : Fin (q + 1)) (φ : (Fin N → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    fieldTranspose (H.fields i) (fieldTranspose (H.fields i) φ) =
      fieldDerivative (H.fields i) (fieldDerivative (H.fields i) φ) := by
  have hd := smooth_fieldDerivative (H.fields i) (H.fields_smooth G i) φ hφ
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fieldTranspose (H.fields i) φ) := by
    rw [H.fieldTranspose_eq_neg G i φ hφ]
    exact hd.neg
  rw [H.fieldTranspose_eq_neg G i _ ht, H.fieldTranspose_eq_neg G i φ hφ]
  funext x
  change -(fderiv ℝ (-(fieldDerivative (H.fields i) φ)) x (H.fields i x)) =
    fderiv ℝ (fieldDerivative (H.fields i) φ) x (H.fields i x)
  rw [fderiv_neg]
  simp

/-- The fixed sum-of-squares transpose is ΣYᵢ²−Y₀
(BB Definition 6.5, p. 254). -/
theorem StandingHypotheses.sumSquaresTranspose_formula (H : StandingHypotheses G q)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin N → ℝ) :
    sumSquaresWithDriftTranspose H.fields φ x =
      -fieldDerivative (H.fields 0) φ x +
        ∑ i : Fin q, fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) φ) x := by
  simp only [sumSquaresWithDriftTranspose, H.fieldTranspose_eq_neg G 0 φ hφ,
    H.squareTranspose G _ φ hφ]
  rfl

end RothschildStein.H1
