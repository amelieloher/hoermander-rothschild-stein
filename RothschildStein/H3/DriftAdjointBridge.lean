-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftTransposeTest
public import RothschildStein.Distribution.AdjointTest
public import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace
open scoped BigOperators

private theorem divergence_fun_neg {n : ℕ}
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    Hormander.Interface.euclideanDivergence (fun y => -V y) x =
      -Hormander.Interface.euclideanDivergence V x := by
  simp only [Hormander.Interface.euclideanDivergence, fderiv_fun_neg,
    neg_apply, Pi.neg_apply, Finset.sum_neg_distrib]

/-- The adjoint `hormanderAdjointTest` with zero multiplier is the exact
drift transpose, including every double negative in the square words. -/
theorem hormanderAdjointTest_zero_eq_driftTranspose {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Hormander.Interface.hormanderAdjointTest X (fun _ => 0) φ x =
      sumSquaresWithDriftTranspose X φ x := by
  simp only [Hormander.Interface.hormanderAdjointTest, sumSquaresWithDriftTranspose,
    fieldTranspose, zero_mul, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => -Hormander.Interface.euclideanDivergence
      (fun z => φ z • X i.succ z) y • X i.succ y) =
      (fun y => -(Hormander.Interface.euclideanDivergence
        (fun z => φ z • X i.succ z) y • X i.succ y)) := by
    funext y
    simp only [neg_smul]
  rw [he, divergence_fun_neg]
  exact (neg_neg _).symm

/-- The bundled H1.HYP adjoint test and the actual weak drift test agree. -/
theorem adjointTest_zero_eq_driftTransposeTest {n q : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Distribution.adjointTest Ω X (fun _ => 0) hX (by fun_prop) ψ =
      driftTransposeTest Ω X hX ψ := by
  ext x
  rw [Distribution.adjointTest_apply, hormanderAdjointTest_zero_eq_driftTranspose,
    driftTransposeTest_apply]

end RothschildStein.H3
