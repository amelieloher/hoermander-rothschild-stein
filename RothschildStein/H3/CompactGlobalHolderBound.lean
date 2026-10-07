-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.H3

/-- Compact support inside an open patch upgrades a local
positive-exponent Hölder bound to a global bound. A compact thickening
provides the separation from the patch complement (BB Prop 8.49). -/
theorem exists_global_holder_bound_of_compact_support
    {X : Type*} [MetricSpace X] {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hsub : tsupport f ⊆ U) {α H : ℝ} (hα : 0 < α)
    (hh : ∀ x ∈ U, ∀ y ∈ U, |f x - f y| ≤ H * dist x y ^ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |f x - f y| ≤ C * dist x y ^ α := by
  obtain ⟨δ, hδ, hthick⟩ := hs.isCompact.exists_cthickening_subset_open hU hsub
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hf
  let C := |H| + |M| / δ ^ α
  have hpow : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) hpow.le)
  have hcross (x y : X) (hy : y ∉ U) :
      |f x - f y| ≤ C * dist x y ^ α := by
    have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hsub h))
    rw [hfy, sub_zero]
    by_cases hfx : f x = 0
    · rw [hfx, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg dist_nonneg _)
    have hd : δ ≤ dist x y := by
      by_contra hn
      exact hy (hthick (mem_cthickening_of_dist_le y x δ (tsupport f)
        (subset_tsupport f hfx) (by rw [dist_comm]; exact (not_le.mp hn).le)))
    calc
      |f x| ≤ |M| := by
        have hxM : |f x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x
        exact hxM.trans (le_abs_self M)
      _ = (|M| / δ ^ α) * δ ^ α := (div_mul_cancel₀ _ hpow.ne').symm
      _ ≤ (|M| / δ ^ α) * dist x y ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hd hα.le)
          (div_nonneg (abs_nonneg _) hpow.le)
      _ ≤ C * dist x y ^ α := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (abs_nonneg H)) (Real.rpow_nonneg dist_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro x y
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_right
        ((le_abs_self H).trans (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hpow.le)))
        (Real.rpow_nonneg dist_nonneg _))
    · exact hcross x y hy
  · by_cases hy : y ∈ U
    · simpa only [abs_sub_comm, dist_comm] using hcross y x hx
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h)),
        image_eq_zero_of_notMem_tsupport (fun h => hy (hsub h)), sub_self, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg dist_nonneg _)

end RothschildStein.H3
