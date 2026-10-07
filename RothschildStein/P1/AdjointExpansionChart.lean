-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.AdjointExpansion
public import RothschildStein.P1.RightPoleComputation

/-!
# Formal adjoint of the lifted fields

The lifted fields `X̃ = C.Xl` of a `LiftedChart` are smooth on the open set `C.U`, so the
transpose of `L̃ = ∑ᵢ X̃ᵢ² + X̃₀` over `C.U` is given by the formal adjoint formula pointwise
(`LiftedChart.sumSquaresWithDriftTranspose_apply`), and `∫ (L̃ f) φ = ∫ f (L̃* φ)` holds for
tests `φ` on `C.U` (`LiftedChart.integral_sumSquaresWithDrift_mul_test`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1
namespace LiftedChart

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The pairing `∫ (L̃ f) φ = ∫ f (L̃* φ)` for the lifted operator over
`C.U`, `f` smooth on `C.U` and `φ` a test function there. -/
theorem integral_sumSquaresWithDrift_mul_test_U (f : (Fin (n + m) → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f C.U)
    (φ : TestFunction (⟨C.U, C.isOpen_U⟩ : Opens (Fin (n + m) → ℝ)) ℝ (⊤ : ℕ∞)) :
    (∫ x in C.U, sumSquaresWithDrift C.Xl f x * φ x) =
      ∫ x in C.U, f x * sumSquaresWithDriftTranspose C.Xl φ x :=
  integral_sumSquaresWithDrift_mul_test ⟨C.U, C.isOpen_U⟩ C.Xl C.contDiffOn_Xl_U f hf φ

end LiftedChart

end RothschildStein.P1
