-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestOperators
public import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ}

/-- The regularized sign is smooth wherever gamma is smooth
(BB Thm 6.3, p. 251; the explicit order-zero to L1 argument). -/
theorem contDiffOn_regularizedSign (Ω : Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ} (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ (Ω : Set (Fin N → ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2))
      (Ω : Set (Fin N → ℝ)) := by
  have hp (x : Fin N → ℝ) : 0 < (γ x) ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg (γ x)]
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Fin N → ℝ => ε ^ 2) (Ω : Set (Fin N → ℝ)) := contDiffOn_const
  have hs := ((hγ.pow 2).add hc).sqrt (fun x _ => (hp x).ne')
  exact hγ.div hs (fun x _ => (Real.sqrt_pos.mpr (hp x)).ne')

/-- The regularized sign has absolute value at most one
(BB p. 251; elementary square-root bound). -/
theorem abs_regularizedSign_le_one (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |a / Real.sqrt (a ^ 2 + ε ^ 2)| ≤ 1 := by
  have hp : 0 < a ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg a]
  have hb : |a| ≤ Real.sqrt (a ^ 2 + ε ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs a]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.mpr hp)).mpr hb

/-- Multiplying the regularized sign by a compact smooth cutoff
gives the actual smooth test needed for the order-zero norm bound
(BB p. 251; reuse of the S multiplier API). -/
def regularizedSignTest (Ω : Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ} (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ (Ω : Set (Fin N → ℝ)))
    {ε : ℝ} (hε : 0 < ε) (χ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    TestFunction Ω ℝ (⊤ : ℕ∞) :=
  testMultiplierOn Ω (fun x => γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2))
    (contDiffOn_regularizedSign Ω hγ hε) χ

/-- Cutoffs between zero and one give tests of uniform norm
at most one (BB p. 251). -/
theorem norm_regularizedSignTest_le_one (Ω : Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ} (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ (Ω : Set (Fin N → ℝ)))
    {ε : ℝ} (hε : 0 < ε) (χ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) (regularizedSignTest Ω hγ hε χ)‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro x
  change ‖χ x * (γ x / Real.sqrt ((γ x) ^ 2 + ε ^ 2))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ x).1]
  exact (mul_le_mul_of_nonneg_left (abs_regularizedSign_le_one (γ x) hε) (hχ x).1).trans
    (by simpa only [mul_one] using (hχ x).2)

end RothschildStein.H1
