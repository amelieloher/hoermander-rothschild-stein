-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalMaxHessian
public import RothschildStein.Definitions.sumSquaresWithDrift
public import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.H1
variable {N q : ℕ}

/-- At a local maximum the squared field contributes only its Hessian
term, which is nonpositive (BB Thm 1.57, pp. 37–38). -/
theorem fieldSquare_nonpos_at_localMax {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (h : IsLocalMax f x)
    (hf : ContDiffAt ℝ 2 f x) (hV : DifferentiableAt ℝ V x) :
    fieldDerivative V (fieldDerivative V f) x ≤ 0 := by
  unfold fieldDerivative
  rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one) hV]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, h.fderiv_eq_zero, zero_apply, zero_add]
  exact IsLocalMax.hessian_nonpos h hf (V x)

/-- A sum of field squares with arbitrary drift is nonpositive
at an interior local maximum (BB Thm 1.57, pp. 37–38). -/
theorem sumSquares_nonpos_at_localMax
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (h : IsLocalMax f x) (hf : ContDiffAt ℝ 2 f x)
    (hX : ∀ i : Fin q, DifferentiableAt ℝ (X i.succ) x) :
    sumSquaresWithDrift X f x ≤ 0 := by
  unfold sumSquaresWithDrift
  have hd : fieldDerivative (X 0) f x = 0 := by
    simp only [fieldDerivative, h.fderiv_eq_zero, zero_apply]
  rw [hd, zero_add]
  apply Finset.sum_nonpos
  intro i _
  exact fieldSquare_nonpos_at_localMax h hf (hX i)

/-- Strict comparison on a bounded open set, stated without
undefined maxima when the set is empty: each closure value is bounded by
a boundary value (BB Thm 1.57, pp. 37–38). -/
theorem strict_comparison_boundary
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f U)
    (hc : ContinuousOn f (closure U))
    (hX : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) U)
    (hP : ∀ x ∈ U, 0 < sumSquaresWithDrift X f x)
    (x : Fin N → ℝ) (hx : x ∈ closure U) :
    ∃ y ∈ frontier U, f x ≤ f y := by
  have hK : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hc
  have hyF : y ∈ frontier U := by
    by_cases hyU : y ∈ U
    · have hm : IsLocalMax f y := by
        filter_upwards [hU.mem_nhds hyU] with z hz
        exact hmax (subset_closure hz)
      have hnf := sumSquares_nonpos_at_localMax hm
        (hf.contDiffAt (hU.mem_nhds hyU))
        (fun i => (hX i y hyU).differentiableAt (hU.mem_nhds hyU))
      exact False.elim ((not_le_of_gt (hP y hyU)) hnf)
    · simpa only [frontier, hU.interior_eq, Set.mem_sdiff] using ⟨hy, hyU⟩
  exact ⟨y, hyF, hmax hx⟩

end RothschildStein.H1
