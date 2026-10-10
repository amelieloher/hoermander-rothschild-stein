-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import RothschildStein.S.LpListSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators
namespace HeatKernel

/-- The difference of two finite Euclidean gradient lengths is bounded by the sum of
the component differences. -/
theorem abs_sqrt_sum_sq_sub_le_sum_abs {q : ℕ} (a b : Fin q → ℝ) :
    |Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)| ≤ ∑ i, |a i - b i| := by
  let A : EuclideanSpace ℝ (Fin q) := WithLp.toLp 2 a
  let B : EuclideanSpace ℝ (Fin q) := WithLp.toLp 2 b
  have hn := abs_norm_sub_norm_le A B
  have hn' : |Real.sqrt (∑ i, a i ^ 2) - Real.sqrt (∑ i, b i ^ 2)| ≤
      Real.sqrt (∑ i, (a i - b i) ^ 2) := by
    simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
      A, B, PiLp.sub_apply, PiLp.toLp_apply] using hn
  apply hn'.trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  simpa only [sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin q => |a i - b i|) (fun i _ => abs_nonneg _))

/-- Finite Euclidean lengths of measurable component functions are measurable. -/
theorem aestronglyMeasurable_sqrt_sum_sq
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {q : ℕ}
    {g : Fin q → A → ℝ} (hg : ∀ j, AEStronglyMeasurable (g j) μ) :
    AEStronglyMeasurable (fun x => Real.sqrt (∑ j, g j x ^ 2)) μ := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  have H := Finset.aestronglyMeasurable_sum (f := fun j x => g j x ^ 2)
    Finset.univ (fun j _ => (continuous_pow 2).comp_aestronglyMeasurable (hg j))
  simpa only [Finset.sum_fn] using H

/-- Componentwise strong Lp convergence implies strong Lp convergence of the finite
Euclidean gradient length. -/
theorem tendsto_eLpNorm_finite_gradient_length
    {A I : Type*} [MeasurableSpace A] {μ : Measure A} {l : Filter I}
    {q : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {F : Fin q → I → A → ℝ} {g : Fin q → A → ℝ}
    (hF : ∀ j i, AEStronglyMeasurable (F j i) μ)
    (hg : ∀ j, AEStronglyMeasurable (g j) μ)
    (h : ∀ j, Tendsto (fun i => eLpNorm (F j i - g j) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => Real.sqrt (∑ j, F j i x ^ 2) - Real.sqrt (∑ j, g j x ^ 2)) p μ)
      l (𝓝 0) := by
  have H : Tendsto (fun i => ∑ j, eLpNorm (F j i - g j) p μ) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => h j)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · exact Eventually.of_forall (fun _ => zero_le)
  · apply Eventually.of_forall
    intro i
    calc
      _ ≤ eLpNorm (fun x => ∑ j, |F j i x - g j x|) p μ := by
        apply eLpNorm_mono ((aestronglyMeasurable_sqrt_sum_sq (fun j => hF j i)).sub
          (aestronglyMeasurable_sqrt_sum_sq hg))
        intro x
        change abs (Real.sqrt (∑ j, F j i x ^ 2) - Real.sqrt (∑ j, g j x ^ 2)) ≤
          abs (∑ j, abs (F j i x - g j x))
        rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg (F j i x - g j x)))]
        exact abs_sqrt_sum_sq_sub_le_sum_abs (fun j => F j i x) (fun j => g j x)
      _ ≤ ∑ j, eLpNorm (fun x => |F j i x - g j x|) p μ := by
        simpa only [Finset.sum_fn] using
          (eLpNorm_sum_le (f := fun j x => |F j i x - g j x|) (s := Finset.univ) hp)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        change eLpNorm (fun x => ‖(F j i - g j) x‖) p μ = eLpNorm (F j i - g j) p μ
        exact eLpNorm_norm (F j i - g j) ((hF j i).sub (hg j))

end HeatKernel
