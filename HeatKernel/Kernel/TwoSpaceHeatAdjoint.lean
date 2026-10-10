-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HeatAdjoint

/-! # The adjoint of the two-space-block heat operator

The union of the horizontal fields on the two spatial blocks is divergence-free.
The drift minus twice the time direction gives twice the positive time derivative
in the adjoint test.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace HeatKernel

open Hormander.Interface RothschildStein RothschildStein.G2

/-- Combining divergence-free fields on separate coordinate blocks preserves zero divergence. -/
theorem euclideanDivergence_sumFields {p q m n : ℕ}
    (X : Fin p → (Fin m → ℝ) → Fin m → ℝ)
    (Y : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hdivX : ∀ i x, euclideanDivergence (X i) x = 0)
    (hdivY : ∀ i x, euclideanDivergence (Y i) x = 0)
    (i : Fin (p + q)) (z : Fin (m + n) → ℝ) :
    euclideanDivergence (sumFields X Y i) z = 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [sumFields_castAdd, euclideanDivergence_liftLeftField n (X j) z
      ((hX j).differentiable (by simp)).differentiableAt, hdivX]
  · rw [sumFields_natAdd, euclideanDivergence_liftRightField m (Y j) z
      ((hY j).differentiable (by simp)).differentiableAt, hdivY]

/-- The adjoint with drift minus twice the time direction has the expected time coefficient. -/
theorem hormanderAdjointTest_twoTimeHeatFields {q n : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hdiv : ∀ i x, euclideanDivergence (X i) x = 0)
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : Fin (1 + n) → ℝ) :
    hormanderAdjointTest (timeSpaceFields (-2) X) 0 φ x =
      2 * fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
      ∑ i : Fin q, fderiv ℝ (fun y => fderiv ℝ φ y (liftRightField 1 (X i) y)) x
        (liftRightField 1 (X i) x) := by
  rw [hormanderAdjointTest_eq_of_divergence_zero _ (contDiff_timeSpaceFields (-2) X hX)
    (euclideanDivergence_timeSpaceFields (-2) X hX hdiv) φ hφ x]
  simp only [timeSpaceFields_zero, timeSpaceFields_succ]
  have heq : (fun _ : Fin 1 => (-2 : ℝ)) = (-2 : ℝ) • (fun _ : Fin 1 => (1 : ℝ)) := by
    ext
    simp
  rw [heq, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The two spatial horizontal families have zero divergence. -/
theorem euclideanDivergence_sumHorizontalFields {n q : ℕ} (G : HomogeneousGroup n)
    (hq : q ≤ n) (i : Fin (q + q)) (x : Fin (n + n) → ℝ) :
    euclideanDivergence (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) x = 0 := by
  have hdiv : ∀ j z, euclideanDivergence (G.horizontalFields hq j) z = 0 := by
    intro j z
    simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
      leftField_divergence_zero G (basisVec (Fin.castLE hq j)) z
  exact euclideanDivergence_sumFields _ _ (G.horizontalFields_contDiff hq)
    (G.horizontalFields_contDiff hq) hdiv hdiv i x

/-- The two-space horizontal heat adjoint has twice the time derivative and both spatial squares. -/
theorem hormanderAdjointTest_horizontalTwoSpaceHeatFields {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : Fin (1 + (n + n)) → ℝ) :
    hormanderAdjointTest (horizontalTwoSpaceHeatFields G hq) 0 φ x =
      2 * fderiv ℝ φ x (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
      ∑ i : Fin (q + q), fderiv ℝ (fun y => fderiv ℝ φ y
        (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) y)) x
        (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) x) := by
  exact hormanderAdjointTest_twoTimeHeatFields _
    (contDiff_sumFields _ _ (G.horizontalFields_contDiff hq) (G.horizontalFields_contDiff hq))
    (euclideanDivergence_sumHorizontalFields G hq) φ hφ x

end HeatKernel
