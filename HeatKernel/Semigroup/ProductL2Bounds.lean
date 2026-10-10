-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.JointLpRepresentatives
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Product square integrability from bounded L² sections -/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace HeatKernel

theorem memLp_joint_representative_of_bounded_L2_sections
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y]
    (σ : Measure α) (μ : Measure Y) [IsFiniteMeasure σ] [SFinite μ]
    [MeasurableSpace (Lp ℝ 2 μ)] [BorelSpace (Lp ℝ 2 μ)]
    (T : α → Lp ℝ 2 μ) (hT : Measurable T) (C : ℝ) (hC : ∀ a, ‖T a‖ ≤ C)
    (u : α × Y → ℝ) (hu : Measurable u)
    (hslice : ∀ a, (fun x => u (a, x)) =ᵐ[μ] T a) :
    MemLp u 2 (σ.prod μ) := by
  have hsection (a : α) : MemLp (fun x => u (a, x)) 2 μ :=
    (memLp_congr_ae (hslice a)).mpr (Lp.memLp (T a))
  have hint (a : α) : (∫ x, ‖u (a, x)‖ ^ 2 ∂μ) = ‖T a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (T a), L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hslice a] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  have hbound : Integrable (fun a => ‖T a‖ ^ 2) σ := by
    apply (integrable_const (C ^ 2)).mono' (hT.norm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro a
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg (T a)).trans (hC a))).mpr (hC a)
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hu.norm.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun a =>
      (memLp_two_iff_integrable_sq_norm (hsection a).aestronglyMeasurable).mp (hsection a))
  · convert hbound using 1
    funext a
    simp only [Real.norm_of_nonneg (sq_nonneg _), hint]

end HeatKernel
