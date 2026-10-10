-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.DivergenceFreeTests
public import RothschildStein.Definitions.sumSquares

/-! # Compact tests under sums of squares

Smooth fields preserve smoothness under their sum of squares, and the
resulting test has no support outside the original test.
-/

@[expose] public section

noncomputable section

open RothschildStein

namespace HeatKernel

/-- A smooth sum of squares preserves smooth scalar tests. -/
theorem contDiff_sumSquares_of_contDiff {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (sumSquares X φ) := by
  exact ContDiff.sum fun i _ => contDiff_fieldDerivative_of_contDiff (X i) (hX i)
    (fieldDerivative (X i) φ) (contDiff_fieldDerivative_of_contDiff (X i) (hX i) φ hφ)

/-- The sum of squares does not enlarge the support of a scalar test. -/
theorem tsupport_sumSquares_subset {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ) :
    tsupport (sumSquares X φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hnot
  apply hx
  have hzero (i : Fin q) : fieldDerivative (X i) (fieldDerivative (X i) φ) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hnot
      (S.tsupport_fieldDerivative_subset (X i) φ
        (S.tsupport_fieldDerivative_subset (X i) (fieldDerivative (X i) φ) h)))
  simp only [sumSquares, hzero, Finset.sum_const_zero]

/-- The sum of squares preserves compact scalar test support. -/
theorem hasCompactSupport_sumSquares {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (hc : HasCompactSupport φ) :
    HasCompactSupport (sumSquares X φ) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_sumSquares_subset X φ)

end HeatKernel
