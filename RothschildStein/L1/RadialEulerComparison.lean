-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LieBracketAddLeft
public import RothschildStein.L1.WeightedEulerInversion
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- The ordinary Euler operator differs from the frame Euler expression
by the actual brackets with the zero-at-origin frame errors. -/
theorem jetEulerOperator_eq_frame_sub_error {N : ℕ}
    (Z : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (W : (Fin N → ℝ) → (Fin N → ℝ)) (u : Fin N → ℝ)
    (hZ : ∀ k, DifferentiableAt ℝ (Z k) u) :
    jetEulerOperator W u =
      ((2 : ℝ) • W u + ∑ k, u k • VectorField.lieBracket ℝ (Z k) W u) -
      ∑ k, u k • VectorField.lieBracket ℝ (fun v => Z k v - Pi.single k 1) W u := by
  have he (k : Fin N) : VectorField.lieBracket ℝ (Z k) W u =
      VectorField.lieBracket ℝ (fun _ => Pi.single k 1) W u +
      VectorField.lieBracket ℝ (fun v => Z k v - Pi.single k 1) W u := by
    have hf : Z k = fun v => (Pi.single k (1 : ℝ) : Fin N → ℝ) +
        (Z k v - Pi.single k 1) := by funext v; abel
    have hh := lieBracket_fun_add_left (fun _ : Fin N → ℝ => Pi.single k 1)
      (fun v => Z k v - Pi.single k 1) W u (differentiableAt_const _)
      ((hZ k).fun_sub (differentiableAt_const _))
    rw [← hf] at hh
    exact hh
  simp_rw [he, smul_add]
  rw [Finset.sum_add_distrib]
  unfold jetEulerOperator
  abel
end RothschildStein.L1
