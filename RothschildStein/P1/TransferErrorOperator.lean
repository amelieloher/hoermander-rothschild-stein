-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeTransferErrorKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The actual positive-type error operator
uses the canonical transfer error kernel, independently of any
regularity decomposition (BB Theorem 11.24, pp. 555–558). -/
def generatorTransferErrorOperator (hF : C.IsLiftedFrame F) {lam : ℕ}
    (T : TypeOperator F lam) (i : Fin k) (hw : (w i : ℕ) ≤ lam) :
    TypeOperator F (lam+1-(w i : ℕ)) where
  kernel := C.cutoffTransferErrorKernel F i T.kernel
  isType := C.isTypeKernel_cutoffTransferErrorKernel F hF T.isType i hw
  mult := 0
  mult_eq_zero := fun _ => rfl

/-- Every transferred input kernel has
strictly positive type, even at the critical output endpoint λ=w_i;
the basis words are nonempty (BB Theorem 11.24, p. 557). -/
theorem generatorTransfer_type_pos {lam : ℕ} (i : Fin k) (j : Fin (n+m))
    (hw : (w i : ℕ) ≤ lam) : 0 < lam + wordWeight w (C.B j) - (w i : ℕ) := by
  have hb : 0 < wordWeight w (C.B j) := by
    have hne := (C.basis_weight j).1
    cases hBj : C.B j with
    | nil => exact False.elim (hne hBj)
    | cons l I => simp only [wordWeight, List.map_cons, List.sum_cons]; exact lt_of_lt_of_le (w l).2 (Nat.le_add_right _ _)
  omega

/-- The canonical error type is strictly
positive at the critical endpoint as well (BB Theorem 11.24, p. 557). -/
theorem generatorTransfer_error_type_pos {lam : ℕ} (i : Fin k)
    (hw : (w i : ℕ) ≤ lam) : 0 < lam+1-(w i : ℕ) := by omega

end RothschildStein.P1.LiftedChart
