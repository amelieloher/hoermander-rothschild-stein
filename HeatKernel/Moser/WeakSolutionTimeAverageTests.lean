-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TimeAverageDerivatives
public import HeatKernel.Bridge.DualTimeBalance

/-!
# Averaged time tests

Backward averages preserve smoothness and enlarge a compact time support only
in the forward direction. These tests pair weak time balances with forward
averages of the solution.
-/

@[expose] public section

open MeasureTheory Set

namespace HeatKernel

/-- A backward average of a smooth scalar time test is smooth. -/
theorem contDiff_backwardTimeAverage {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (backwardTimeAverage h ψ) := by
  have hd := hasDerivAt_backwardTimeAverage_of_continuous hψ.continuous h
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (backwardTimeAverage h ψ) =
      fun t => h⁻¹ • (ψ t - ψ (t - h)) := funext fun t => (hd t).deriv
  rw [he]
  exact (hψ.sub (hψ.comp (contDiff_id.sub contDiff_const))).const_smul h⁻¹

/-- A nonnegative averaging length enlarges the support only to the right. -/
theorem tsupport_backwardTimeAverage_subset {ψ : ℝ → ℝ} {a b h : ℝ}
    (hψ : tsupport ψ ⊆ Icc a b) (hh : 0 ≤ h) :
    tsupport (backwardTimeAverage h ψ) ⊆ Icc a (b + h) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have hz : backwardTimeAverage h ψ t = 0 := by
    unfold backwardTimeAverage
    have he : (∫ s in t - h..t, ψ s) = ∫ s in t - h..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : t - h ≤ s ∧ s ≤ t := by
        simpa only [uIcc_of_le (sub_le_self t hh), mem_Icc] using hs
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hab := hψ hm
      have ht' : t < a ∨ b + h < t := by
        simpa only [mem_Icc, not_and_or, not_le] using hn
      rcases ht' with hl | hr <;> linarith [hab.1, hab.2, hs'.1, hs'.2]
    rw [he, intervalIntegral.integral_zero, smul_zero]
  exact ht hz

/-- Backward averages of tests supported in a bounded interval remain compactly supported. -/
theorem hasCompactSupport_backwardTimeAverage {ψ : ℝ → ℝ} {a b h : ℝ}
    (hψ : tsupport ψ ⊆ Icc a b) (hh : 0 ≤ h) :
    HasCompactSupport (backwardTimeAverage h ψ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_backwardTimeAverage_subset hψ hh)

end HeatKernel
