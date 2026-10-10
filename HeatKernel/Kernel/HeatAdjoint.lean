-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HorizontalSpacetime
public import RothschildStein.G2.InvariantDivergence
public import Hormander.F.Transpose

/-! # Adjoint tests for divergence-free heat fields

The divergence product rule identifies the formal adjoint with the time derivative
and the sum of horizontal second derivatives.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace HeatKernel

open Hormander.Interface RothschildStein RothschildStein.G2

/-- For a divergence-free field, the localized divergence is its directional derivative. -/
theorem euclideanDivergence_smul_eq_fderiv {n : ℕ}
    (V : (Fin n → ℝ) → Fin n → ℝ) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hdiv : ∀ x, euclideanDivergence V x = 0)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin n → ℝ) :
    euclideanDivergence (fun y => φ y • V y) x = fderiv ℝ φ x (V x) := by
  rw [Hormander.F.localizedDivergence_product_rule isOpen_univ V hV.contDiffOn φ hφ
    (Set.subset_univ _) x, hdiv x, MulZeroClass.mul_zero, add_zero]

/-- The zero-potential formal adjoint is the sum of directional squares minus the drift. -/
theorem hormanderAdjointTest_eq_of_divergence_zero {q n : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hdiv : ∀ i x, euclideanDivergence (X i) x = 0)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin n → ℝ) :
    hormanderAdjointTest X 0 φ x = -fderiv ℝ φ x (X 0 x) +
      ∑ i : Fin q, fderiv ℝ (fun y => fderiv ℝ φ y (X i.succ y)) x (X i.succ x) := by
  simp only [hormanderAdjointTest, Pi.zero_apply, MulZeroClass.zero_mul, add_zero]
  rw [euclideanDivergence_smul_eq_fderiv (X 0) (hX 0) (hdiv 0) φ hφ x]
  apply congrArg (fun s : ℝ => -fderiv ℝ φ x (X 0 x) + s)
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y => euclideanDivergence (fun z => φ z • X i.succ z) y) =
      fun y => fderiv ℝ φ y (X i.succ y) := by
    funext y
    exact euclideanDivergence_smul_eq_fderiv _ (hX i.succ) (hdiv i.succ) φ hφ y
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ φ y (X i.succ y)) := by
    rw [← heq]
    exact Hormander.F.localizedDivergence_smooth isOpen_univ _ (hX i.succ).contDiffOn
      φ hφ (Set.subset_univ _)
  change euclideanDivergence
    (fun y => (fun y => euclideanDivergence (fun z => φ z • X i.succ z) y) y • X i.succ y) x = _
  rw [heq]
  exact euclideanDivergence_smul_eq_fderiv _ (hX i.succ) (hdiv i.succ) _ hd x

/-- Adding a constant time field preserves the zero divergences of the spatial generators. -/
theorem euclideanDivergence_timeSpaceFields {q n : ℕ} (c : ℝ)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hdiv : ∀ i x, euclideanDivergence (X i) x = 0)
    (i : Fin (q + 1)) (x : Fin (1 + n) → ℝ) :
    euclideanDivergence (timeSpaceFields c X i) x = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [timeSpaceFields_zero]
    simp [euclideanDivergence]
  · rw [timeSpaceFields_succ, euclideanDivergence_liftRightField 1 (X j) x
      ((hX j).differentiable (by simp)).differentiableAt]
    exact hdiv j _

/-- The negative unit time drift produces the positive time derivative in the adjoint test. -/
theorem hormanderAdjointTest_heatFields {q n : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hdiv : ∀ i x, euclideanDivergence (X i) x = 0)
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : Fin (1 + n) → ℝ) :
    hormanderAdjointTest (timeSpaceFields (-1) X) 0 φ x =
      fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
      ∑ i : Fin q, fderiv ℝ (fun y => fderiv ℝ φ y (liftRightField 1 (X i) y)) x
        (liftRightField 1 (X i) x) := by
  rw [hormanderAdjointTest_eq_of_divergence_zero _ (contDiff_timeSpaceFields (-1) X hX)
    (euclideanDivergence_timeSpaceFields (-1) X hX hdiv) φ hφ x]
  simp only [timeSpaceFields_zero, timeSpaceFields_succ]
  have heq : (fun _ : Fin 1 => (-1 : ℝ)) = -(fun _ : Fin 1 => (1 : ℝ)) := rfl
  rw [heq, map_neg, map_neg, neg_neg]

/-- The group heat adjoint has a positive time derivative and the lifted horizontal squares. -/
theorem hormanderAdjointTest_horizontalHeatFields {n q : ℕ} (G : HomogeneousGroup n)
    (hq : q ≤ n) (φ : (Fin (1 + n) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin (1 + n) → ℝ) :
    hormanderAdjointTest (horizontalHeatFields G hq) 0 φ x =
      fderiv ℝ φ x (leftCoordinateInclusion 1 n (fun _ => 1)) +
      ∑ i : Fin q, fderiv ℝ
        (fun y => fderiv ℝ φ y (liftRightField 1 (G.horizontalFields hq i) y)) x
        (liftRightField 1 (G.horizontalFields hq i) x) := by
  apply hormanderAdjointTest_heatFields _ (G.horizontalFields_contDiff hq) _ φ hφ x
  intro j z
  simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
    leftField_divergence_zero G (basisVec (Fin.castLE hq j)) z

end HeatKernel
