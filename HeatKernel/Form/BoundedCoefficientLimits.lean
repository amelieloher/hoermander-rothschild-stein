-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.DominatedL2
public import HeatKernel.Form.SmoothGraphLimits
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Tactic.Linarith

/-!
# L² limits of bounded scalar coefficients

Uniformly bounded coefficients whose products with a fixed L² function converge almost
everywhere may be multiplied by L² factors without losing convergence in L².
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HeatKernel

/-- Bounded coefficients whose products with a fixed L² function converge almost everywhere
give L² convergence of the product error. -/
theorem tendsto_eLpNorm_two_mul_of_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {a : ℕ → α → ℝ} {b g : α → ℝ} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (hg : MemLp g 2 μ) (hC : 0 ≤ C)
    (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C) (hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x * g x) atTop (𝓝 (b x * g x))) :
    Tendsto (fun n => eLpNorm (fun x => (a n x - b x) * g x) 2 μ) atTop (𝓝 0) := by
  apply tendsto_eLpNorm_two_zero_of_dominated
    (fun n => ((ha n).sub hb).mul hg.aestronglyMeasurable) (hg.norm.const_mul (2 * C))
  · intro n
    filter_upwards [hab n, hbb] with x hx hy
    calc
      ‖(a n x - b x) * g x‖ = ‖a n x - b x‖ * ‖g x‖ := norm_mul _ _
      _ ≤ (‖a n x‖ + ‖b x‖) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ (2 * C) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ = ‖(2 * C) * ‖g x‖‖ := (Real.norm_of_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hC) (norm_nonneg _))).symm
  · filter_upwards [ht] with x hx
    simpa only [sub_mul, sub_self, Pi.sub_apply, Pi.mul_apply] using hx.sub_const (b x * g x)

/-- Bounded coefficients preserve L² convergence of the factors when their products with the
limiting factor converge almost everywhere. -/
theorem tendsto_L2_mul_of_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : ℕ → α → ℝ} {b : α → ℝ} {g : ℕ → Lp ℝ 2 μ} {h : Lp ℝ 2 μ}
    {u : ℕ → Lp ℝ 2 μ} {v : Lp ℝ 2 μ} {C : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    (hC : 0 ≤ C) (hab : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (hbb : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x * h x) atTop (𝓝 (b x * h x)))
    (hg : Tendsto g atTop (𝓝 h))
    (hu : ∀ n, u n =ᵐ[μ] fun x => a n x * g n x)
    (hv : v =ᵐ[μ] fun x => b x * h x) : Tendsto u atTop (𝓝 v) := by
  have hm : ∀ n, MemLp (fun x => a n x * h x) 2 μ := by
    intro n
    apply ((Lp.memLp h).const_mul C).of_le ((ha n).mul (Lp.memLp h).aestronglyMeasurable)
    filter_upwards [hab n] with x hx
    simpa only [Pi.mul_apply, norm_mul, Real.norm_of_nonneg hC] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (h x))
  let z : ℕ → Lp ℝ 2 μ := fun n => (hm n).toLp (fun x => a n x * h x)
  have hz : ∀ n, z n =ᵐ[μ] fun x => a n x * h x := fun n => (hm n).coeFn_toLp
  have hzt : Tendsto z atTop (𝓝 v) := by
    apply tendsto_L2_of_representatives hz hv
    have H := tendsto_eLpNorm_two_mul_of_bounded ha hb (Lp.memLp h) hC hab hbb ht
    simpa only [Pi.sub_def, sub_mul] using H
  have he : ∀ n, ‖u n - z n‖ ≤ C * ‖g n - h‖ := by
    intro n
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hu n, hz n, hab n, Lp.coeFn_sub (u n) (z n), Lp.coeFn_sub (g n) h]
      with x hux hzx hx hus hgs
    simp only [Pi.sub_apply] at hus hgs
    rw [hus, hux, hzx, ← mul_sub, norm_mul, hgs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have het : Tendsto (fun n => ‖u n - z n‖) atTop (𝓝 0) := by
    have H := (hg.sub (tendsto_const_nhds (x := h))).norm.const_mul C
    simp only [sub_self, norm_zero, mul_zero] at H
    exact squeeze_zero (fun _ => norm_nonneg _) he H
  have hd : Tendsto (fun n => u n - z n) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr het
  simpa only [sub_add_cancel, zero_add] using hd.add hzt

end HeatKernel
