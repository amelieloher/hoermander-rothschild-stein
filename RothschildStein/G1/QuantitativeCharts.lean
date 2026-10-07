-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped NNReal

namespace RothschildStein.G1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative closeness estimate implies linear approximation on
any convex parameter domain (BB Thm 1.43, pp. 24–25; quantitative chart step). -/
theorem chart_approximatesLinearOn_of_derivative_bound {f : E → F}
    {D : E → E →L[ℝ] F} {A : E →L[ℝ] F} {s : Set E} {c : ℝ≥0}
    (hs : Convex ℝ s) (hD : ∀ x ∈ s, HasFDerivAt f (D x) x)
    (hbound : ∀ x ∈ s, ‖D x - A‖ ≤ c) :
    ApproximatesLinearOn f A s c := by
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => f z - A z) (f' := fun z => D z - A)
    (fun z hz => ((hD z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hbound hs hy hx
  have heq : f x - A x - (f y - A y) = f x - f y - A (x - y) := by
    rw [map_sub]; abel
  rwa [heq] at h

/-- Derivative closeness gives the inverse parameter estimate with
constant 2P, before constructing the inverse (BB Thm 1.43, pp. 24–25). -/
theorem chart_inverse_parameter_bound {f : E → F} {D : E → E →L[ℝ] F}
    (A : E ≃L[ℝ] F) {s : Set E} {P : ℝ} (hP : 0 < P)
    (hA : ‖(A.symm : F →L[ℝ] E)‖ ≤ P) (hs : Convex ℝ s)
    (hD : ∀ x ∈ s, HasFDerivAt f (D x) x)
    (hbound : ∀ x ∈ s, ‖D x - (A : E →L[ℝ] F)‖ ≤ 1 / (2 * P))
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖x - y‖ ≤ 2 * P * ‖f x - f y‖ := by
  let c : ℝ≥0 := ⟨1 / (2 * P), by positivity⟩
  have hf := chart_approximatesLinearOn_of_derivative_bound (c := c) hs hD hbound
  have he := hf x hx y hy
  have ha : ‖x - y‖ ≤ P * ‖A (x - y)‖ := by
    calc
      ‖x - y‖ = ‖A.symm (A (x - y))‖ := by rw [A.symm_apply_apply]
      _ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖A (x - y)‖ := (A.symm : F →L[ℝ] E).le_opNorm _
      _ ≤ P * ‖A (x - y)‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  have hb : ‖A (x - y)‖ ≤ ‖f x - f y‖ + (1 / (2 * P)) * ‖x - y‖ := by
    calc
      ‖A (x - y)‖ ≤ ‖f x - f y‖ + ‖f x - f y - A (x - y)‖ := by
        have ht := norm_sub_le (f x - f y) (f x - f y - A (x - y))
        simpa only [sub_sub_cancel] using ht
      _ ≤ _ := add_le_add_right he _
  have hh := ha.trans (mul_le_mul_of_nonneg_left hb hP.le)
  have hp : P * (1 / (2 * P)) = 1 / 2 := by field_simp
  rw [mul_add, ← mul_assoc, hp] at hh
  linarith

/-- Quantitative derivative closeness implies injectivity on the
parameter domain (BB Thm 1.43, pp. 24–25). -/
theorem chart_injOn_of_derivative_bound {f : E → F} {D : E → E →L[ℝ] F}
    (A : E ≃L[ℝ] F) {s : Set E} {P : ℝ} (hP : 0 < P)
    (hA : ‖(A.symm : F →L[ℝ] E)‖ ≤ P) (hs : Convex ℝ s)
    (hD : ∀ x ∈ s, HasFDerivAt f (D x) x)
    (hbound : ∀ x ∈ s, ‖D x - (A : E →L[ℝ] F)‖ ≤ 1 / (2 * P)) :
    InjOn f s := by
  intro x hx y hy hxy
  have h := chart_inverse_parameter_bound A hP hA hs hD hbound hx hy
  rw [hxy, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- A quantitative chart has its whole parameter ball as source and
contains the closed image ball of radius r/(4P). The zero dimensional case
is included (BB Thm 1.43, pp. 24–25; quantitative inverse theorem). -/
theorem chart_exists_openPartialHomeomorph_of_derivative_bound [CompleteSpace E]
    {f : E → F} {D : E → E →L[ℝ] F} (A : E ≃L[ℝ] F)
    {r P : ℝ} (hr : 0 < r) (hP : 0 < P)
    (hA : ‖(A.symm : F →L[ℝ] E)‖ ≤ P)
    (hD : ∀ x ∈ ball (0 : E) r, HasFDerivAt f (D x) x)
    (hbound : ∀ x ∈ ball (0 : E) r,
      ‖D x - (A : E →L[ℝ] F)‖ ≤ 1 / (2 * P)) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ e.source = ball 0 r ∧
      closedBall (f 0) (r / (4 * P)) ⊆ e.target := by
  let c : ℝ≥0 := ⟨1 / (2 * P), by positivity⟩
  have hf := chart_approximatesLinearOn_of_derivative_bound
    (c := c) (convex_ball (0 : E) r) hD hbound
  rcases subsingleton_or_nontrivial E with hE | hE
  · let := hE
    let e := hf.toOpenPartialHomeomorph f (ball 0 r) (Or.inl hE) isOpen_ball
    refine ⟨e, rfl, rfl, ?_⟩
    have hF : Subsingleton F := (Equiv.subsingleton_congr A.toEquiv).mp hE
    intro y hy
    change y ∈ f '' ball 0 r
    exact ⟨0, mem_ball_self hr, hF.elim _ _⟩
  · let := hE
    have hn := A.norm_symm_pos
    have hni : 1 / P ≤ ‖(A.symm : F →L[ℝ] E)‖⁻¹ := by
      simpa only [one_div] using inv_anti₀ hn hA
    have hc : c < ‖(A.symm : F →L[ℝ] E)‖₊⁻¹ := by
      change 1 / (2 * P) < ‖(A.symm : F →L[ℝ] E)‖⁻¹
      exact lt_of_lt_of_le (by apply one_div_lt_one_div_of_lt hP; linarith) hni
    let e := hf.toOpenPartialHomeomorph f (ball 0 r) (Or.inr hc) isOpen_ball
    refine ⟨e, rfl, rfl, ?_⟩
    have hs : closedBall (0 : E) (r / 2) ⊆ ball 0 r :=
      closedBall_subset_ball (by linarith)
    have ht := hf.closedBall_subset_target (Or.inr hc) isOpen_ball
      (show 0 ≤ r / 2 by positivity) hs
    apply Subset.trans (closedBall_subset_closedBall ?_) ht
    change r / (4 * P) ≤ (‖(A.symm : F →L[ℝ] E)‖⁻¹ - 1 / (2 * P)) * (r / 2)
    calc
      r / (4 * P) = (1 / P - 1 / (2 * P)) * (r / 2) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hni _) (by positivity)

end RothschildStein.G1
