-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PolynomialTranslation
public import RothschildStein.L1.TranslatedFreeness
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.P1.PaddingCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Translate a triangular coefficient array back from centered coordinates. -/
def recenteredLiftPolynomials {a n m : ℕ}
    (P : Fin a → Fin m → MvPolynomial (Fin (n+m)) ℝ) (x : Fin n → ℝ) :=
  fun i l => translatedPolynomial (P i l) (-joinPoint x (0 : Fin m → ℝ))

/-- Translation back preserves the variable-support condition. -/
theorem recenteredLiftPolynomials_vars {a n m : ℕ}
    (P : Fin a → Fin m → MvPolynomial (Fin (n+m)) ℝ) (x : Fin n → ℝ)
    (hP : ∀ i l, ∀ j ∈ (P i l).vars, j.val < n+l.val) :
    ∀ i l, ∀ j ∈ (recenteredLiftPolynomials P x i l).vars, j.val < n+l.val := by
  intro i l j hj
  exact hP i l j (translatedPolynomial_vars_subset _ _ hj)

/-- Translating the centered polynomial lift back restores the
original horizontal fields exactly (BB Theorem 10.19). -/
theorem triangularLift_recentered {a n m : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n+m)) ℝ) (x : Fin n → ℝ) :
    triangularLift X (recenteredLiftPolynomials P x) =
      translatedFields (triangularLift (translatedFields X x) P)
        (-joinPoint x (0 : Fin m → ℝ)) := by
  funext i ξ j
  have hb : basePoint (ξ + -joinPoint x (0 : Fin m → ℝ)) + x = basePoint ξ := by
    ext k
    simp only [basePoint,Pi.add_apply,Pi.neg_apply,joinPoint,Fin.addCases_left]
    ring
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [triangularLift,translatedFields,Fin.addCases_left]
    rw [hb]
  · intro l
    simp only [triangularLift,translatedFields,Fin.addCases_right,recenteredLiftPolynomials]
    exact translatedPolynomial_eval _ _ _
end RothschildStein.L1
