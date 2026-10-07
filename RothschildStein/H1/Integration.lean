-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Transpose
public import RothschildStein.S.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open MeasureTheory TopologicalSpace
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- C¹ integration by parts against the actual compact smooth tests on an open set
(BB Remark 3.30, p. 111; local test-function form). -/
theorem StandingHypotheses.integral_field_test (H : StandingHypotheses G q)
    (U : Opens (Fin N → ℝ)) (i : Fin (q + 1)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ 1 f (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x in (U : Set (Fin N → ℝ)), fieldDerivative (H.fields i) f x * φ x) =
      -(∫ x in (U : Set (Fin N → ℝ)), f x * fieldDerivative (H.fields i) φ x) := by
  have h := S.integral_fieldDerivative_mul_test U (H.fields i) (H.fields_smooth G i).contDiffOn f hf φ
  rw [H.fieldTranspose_eq_neg G i φ φ.contDiff] at h
  simpa only [Pi.neg_apply, mul_neg, integral_neg] using h

/-- C² integration by parts for a squared invariant field, against compact smooth tests
(BB p. 254; local test-function form). -/
theorem StandingHypotheses.integral_square_test (H : StandingHypotheses G q)
    (U : Opens (Fin N → ℝ)) (i : Fin (q + 1)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ 2 f (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x in (U : Set (Fin N → ℝ)),
      fieldDerivative (H.fields i) (fieldDerivative (H.fields i) f) x * φ x) =
      ∫ x in (U : Set (Fin N → ℝ)),
        f x * fieldDerivative (H.fields i) (fieldDerivative (H.fields i) φ) x := by
  have hdf : ContDiffOn ℝ 1 (fieldDerivative (H.fields i) f) (U : Set (Fin N → ℝ)) :=
    (hf.fderiv_of_isOpen U.isOpen (by norm_num)).clm_apply
      ((H.fields_smooth G i).of_le (by simp)).contDiffOn
  let ψ := fieldTransposeTest U (H.fields i) (H.fields_smooth G i).contDiffOn φ
  have hψ : (ψ : (Fin N → ℝ) → ℝ) = fieldTranspose (H.fields i) φ := by
    funext x
    exact S.fieldTransposeTest_apply U _ _ φ x
  have h1 := S.integral_fieldDerivative_mul_test U (H.fields i)
    (H.fields_smooth G i).contDiffOn (fieldDerivative (H.fields i) f) hdf φ
  have h2 := S.integral_fieldDerivative_mul_test U (H.fields i)
    (H.fields_smooth G i).contDiffOn f (hf.of_le (by norm_num)) ψ
  rw [hψ] at h2
  rw [h2, H.squareTranspose G i φ φ.contDiff] at h1
  exact h1

end RothschildStein.H1
