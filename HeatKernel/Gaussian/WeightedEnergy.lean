-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Weighted energy and exponential growth

Completing the square in the horizontal gradient gives the weighted energy
inequality. An integrating factor proves the growth bound directly on a closed
time interval, requiring differentiability only at positive interior times.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open scoped BigOperators
namespace HeatKernel.Gaussian

/-- Completion of the square in a weighted horizontal energy integrand. -/
theorem weighted_gradient_identity {ι : Type*} [Fintype ι]
    (g h : ι → ℝ) (a u : ℝ) :
    (∑ i, (g i + a * u * h i) ^ 2) - a ^ 2 * u ^ 2 * (∑ i, h i ^ 2) =
      ∑ i, g i * (g i + 2 * a * u * h i) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A unit gradient bound controls the negative weighted energy integrand. -/
theorem neg_two_weighted_gradient_le {ι : Type*} [Fintype ι]
    (g h : ι → ℝ) (a u : ℝ) (hh : ∑ i, h i ^ 2 ≤ 1) :
    -2 * (∑ i, g i * (g i + 2 * a * u * h i)) ≤ 2 * a ^ 2 * u ^ 2 := by
  have hs : 0 ≤ ∑ i, (g i + a * u * h i) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg a) (sq_nonneg u))
  have hi := weighted_gradient_identity g h a u
  nlinarith

/-- A continuous energy with an interior differential inequality has exponential
growth controlled by its value at time zero. -/
theorem le_exp_mul_initial_of_derivative_le {F F' : ℝ → ℝ} {K t : ℝ}
    (ht : 0 ≤ t) (hF : ContinuousOn F (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt F (F' s) s)
    (hbound : ∀ s ∈ Ioo 0 t, F' s ≤ K * F s) :
    F t ≤ Real.exp (K * t) * F 0 := by
  let g : ℝ → ℝ := fun s => Real.exp (-K * s) * F s
  have hg : ContinuousOn g (Icc 0 t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hF
  have hd : ∀ s ∈ interior (Icc 0 t),
      HasDerivWithinAt g (Real.exp (-K * s) * (F' s - K * F s)) (interior (Icc 0 t)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have H := (((hasDerivAt_id s).const_mul (-K)).exp).mul (hderiv s hs)
    apply HasDerivAt.hasDerivWithinAt
    convert H using 1
    · rfl
    · dsimp
      ring
  have hb : ∀ s ∈ interior (Icc 0 t), Real.exp (-K * s) * (F' s - K * F s) ≤ 0 := by
    intro s hs
    rw [interior_Icc] at hs
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (sub_nonpos.mpr (hbound s hs))
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hg hd hb
  have hz : g t ≤ F 0 := by
    simpa [g] using ha (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht⟩)
      (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩) ht
  calc
    F t = Real.exp (K * t) * g t := by
      dsimp [g]
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (K * t) * F 0 := mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)

/-- Weighted Hilbert trajectories satisfy the Davies norm bound once their
energy differential inequality and continuity at zero are supplied. -/
theorem norm_le_exp_mul_initial_of_inner_derivative_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {u u' : ℝ → H} {a t : ℝ}
    (ht : 0 ≤ t) (hu : ContinuousOn u (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt u (u' s) s)
    (henergy : ∀ s ∈ Ioo 0 t, inner ℝ (u s) (u' s) ≤ a ^ 2 * ‖u s‖ ^ 2) :
    ‖u t‖ ≤ Real.exp (a ^ 2 * t) * ‖u 0‖ := by
  have hg := le_exp_mul_initial_of_derivative_le (F := fun s => ‖u s‖ ^ 2)
    (F' := fun s => 2 * inner ℝ (u s) (u' s)) (K := 2 * a ^ 2) ht
    (hu.norm.pow 2) (fun s hs => (hderiv s hs).norm_sq)
    (fun s hs => by have := henergy s hs; nlinarith)
  have he : Real.exp (2 * a ^ 2 * t) = Real.exp (a ^ 2 * t) ^ 2 := by
    rw [sq (Real.exp _), ← Real.exp_add]
    congr 1
    ring
  rw [he] at hg
  have hp : 0 ≤ Real.exp (a ^ 2 * t) * ‖u 0‖ := by positivity
  nlinarith [norm_nonneg (u t)]

/-- A bounded operator has the Davies norm bound when each of its trajectories
has the weighted energy inequality and starts from the input vector. -/
theorem opNorm_le_exp_of_energy_trajectories {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (u u' : H → ℝ → H) {a t : ℝ} (ht : 0 ≤ t)
    (hzero : ∀ f, u f 0 = f) (htime : ∀ f, u f t = T f)
    (hcont : ∀ f, ContinuousOn (u f) (Icc 0 t))
    (hderiv : ∀ f s, s ∈ Ioo 0 t → HasDerivAt (u f) (u' f s) s)
    (henergy : ∀ f s, s ∈ Ioo 0 t →
      inner ℝ (u f s) (u' f s) ≤ a ^ 2 * ‖u f s‖ ^ 2) :
    ‖T‖ ≤ Real.exp (a ^ 2 * t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_nonneg _)
  intro f
  simpa only [hzero, htime] using
    norm_le_exp_mul_initial_of_inner_derivative_le ht (hcont f) (hderiv f) (henergy f)

end HeatKernel.Gaussian
