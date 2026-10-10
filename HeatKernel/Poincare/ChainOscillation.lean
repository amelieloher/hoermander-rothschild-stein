-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WalkTelescoping
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Tactic.Ring

/-! Oscillation estimates obtained by telescoping constants along a simple path. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace HeatKernel

/-- A local oscillation bound and endpoint-weighted edge bounds give a root-constant
oscillation estimate with three times the sum of the vertex costs. -/
theorem eLpNorm_sub_le_three_mul_simple_path_cost {E ι : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (U : Set E) (G : SimpleGraph ι)
    (c e : ι → ℝ) (he : ∀ k, 0 ≤ e k) {K : ℝ} (hK : 0 ≤ K)
    (hstep : ∀ k l, G.Adj k l → |c k - c l| ≤ K * (e k + e l))
    {i j : ι} (w : G.Walk i j) (hw : w.IsPath)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (hlocal : eLpNorm (fun x => f x - c i) p (μ.restrict U) ≤
      ENNReal.ofReal (K * e i) * μ U ^ (1 / p.toReal)) :
    eLpNorm (fun x => f x - c j) p (μ.restrict U) ≤
      ENNReal.ofReal (3 * K * ∑ k ∈ w.support.toFinset, e k) *
        μ U ^ (1 / p.toReal) := by
  classical
  let S := ∑ k ∈ w.support.toFinset, e k
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ => he k)
  have hiS : e i ≤ S := Finset.single_le_sum (fun k _ => he k)
    (List.mem_toFinset.mpr w.start_mem_support)
  have ht := abs_sub_le_two_mul_simple_path_sum G c (fun k => K * e k)
    (fun k => mul_nonneg hK (he k)) (by
      intro k l hkl
      simpa only [mul_add] using hstep k l hkl) w hw
  rw [← Finset.mul_sum] at ht
  have htel : |c i - c j| ≤ 2 * K * S := by
    simpa only [S, mul_assoc] using ht
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hp).ne'
  have hconst : eLpNorm (fun _ : E => c i - c j) p (μ.restrict U) ≤
      ENNReal.ofReal (2 * K * S) * μ U ^ (1 / p.toReal) := by
    rw [eLpNorm_const' (c i - c j) hp0 hptop, Measure.restrict_apply_univ,
      Real.enorm_eq_ofReal_abs]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal htel) _
  have heq : (fun x => f x - c j) =
      (fun x => f x - c i) + (fun _ : E => c i - c j) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [heq]
  refine (eLpNorm_add_le hp).trans ((add_le_add hlocal hconst).trans ?_)
  rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hK (he i))
    (mul_nonneg (mul_nonneg (by norm_num) hK) hS)]
  apply mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  change K * e i + 2 * K * S ≤ 3 * K * S
  nlinarith [mul_le_mul_of_nonneg_left hiS hK]

end HeatKernel
