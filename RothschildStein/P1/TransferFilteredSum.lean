-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferErrorOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MvPolynomial MeasureTheory
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- Every below-weight canonical transfer
kernel vanishes identically, before any operator limit (BB Lemma 11.23). -/
theorem generatorTransferKernel_zero_of_basisWeight_lt (i : Fin k) (j : Fin (n+m))
    (hj : wordWeight w (C.B j) < (w i : ℕ))
    (κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ) :
    C.generatorTransferKernel F i j κ = fun _ _ => 0 := by
  have hz := C.generatorTransferCoefficient_zero_of_weight_lt i j
    (by rwa [(C.basis_weight j).2.2])
  funext ξ η
  simp only [generatorTransferKernel, hz, map_zero, zero_mul]

/-- Below-weight canonical transfer operators
act as zero, so they contribute no diagonal term (BB Theorem 11.24). -/
theorem generatorTransferOperator_apply_zero_of_basisWeight_lt
    (hF : C.IsLiftedFrame F) {lam : ℕ} (T : TypeOperator F lam)
    (i : Fin k) (j : Fin (n+m)) (hw : (w i : ℕ) ≤ lam)
    (hj : wordWeight w (C.B j) < (w i : ℕ))
    (f : (Fin (n+m) → ℝ) → ℝ) (ξ : Fin (n+m) → ℝ) :
    (C.generatorTransferOperator F hF T i j).apply f ξ = 0 := by
  have hn := (C.generatorTransfer_type_pos i j hw).ne'
  simp only [TypeOperator.apply, ite_eq_right hn, generatorTransferOperator,
    C.generatorTransferKernel_zero_of_basisWeight_lt F i j hj T.kernel,
    zero_mul, integral_zero]

/-- The full transfer sum is exactly the
weight-filtered sum in the transfer hypothesis `DerivativeTransfer`. -/
theorem generatorTransferOperator_sum_eq_filtered
    (hF : C.IsLiftedFrame F) {lam : ℕ} (T : TypeOperator F lam)
    (i : Fin k) (hw : (w i : ℕ) ≤ lam)
    (f : Fin (n+m) → (Fin (n+m) → ℝ) → ℝ) (ξ : Fin (n+m) → ℝ) :
    (∑ j, (C.generatorTransferOperator F hF T i j).apply (f j) ξ) =
      ∑ j ∈ Finset.univ.filter (fun j => (w i : ℕ) ≤ wordWeight w (C.B j)),
        (C.generatorTransferOperator F hF T i j).apply (f j) ξ := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  have hlt : wordWeight w (C.B j) < (w i : ℕ) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hj
  exact C.generatorTransferOperator_apply_zero_of_basisWeight_lt F hF T i j hw hlt (f j) ξ

end RothschildStein.P1.LiftedChart
