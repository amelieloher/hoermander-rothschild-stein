-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (Ω : Opens (Fin N → ℝ))

private theorem zero_on_test_vanishing_at_origin
    (T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ, |T φ| ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖)
    (haway : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), (0 : Fin N → ℝ) ∉ tsupport (φ : (Fin N → ℝ) → ℝ) → T φ = 0)
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) (hψ : ψ 0 = 0) : T ψ = 0 := by
  have hsmall (ε : ℝ) (hε : 0 < ε) : |T ψ| ≤ C * ε := by
    have ht := ψ.contDiff.continuous.tendsto (0 : Fin N → ℝ)
    rw [hψ] at ht
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
      (ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hε))
    let b : ContDiffBump (0 : Fin N → ℝ) :=
      { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
    let χ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
      ⟨fun x => ψ x * b x, ψ.contDiff.mul b.contDiff, ψ.hasCompactSupport.mul_right,
        tsupport_mul_subset_left.trans ψ.tsupport_subset⟩
    have hzero : (0 : Fin N → ℝ) ∉ tsupport ((ψ - χ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
        (Fin N → ℝ) → ℝ) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [b.eventuallyEq_one] with x hx
      change ψ x - ψ x * b x = 0
      change b x = 1 at hx
      rw [hx, mul_one, sub_self]
    have he : T ψ = T χ := by
      have H := haway (ψ - χ) hzero
      rw [map_sub] at H
      exact sub_eq_zero.mp H
    have hn : ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) χ‖ ≤ ε := by
      apply (BoundedContinuousFunction.norm_le hε.le).mpr
      intro x
      change ‖ψ x * b x‖ ≤ ε
      by_cases hx : b x = 0
      · simp only [hx, mul_zero, norm_zero]; exact hε.le
      · have hb : x ∈ Metric.ball (0 : Fin N → ℝ) r := by
          have H : x ∈ Function.support b := hx
          simpa only [b.support_eq] using H
        have hψx : ‖ψ x‖ ≤ ε := by
          have H := hball hb
          change dist (ψ x) 0 < ε at H
          rw [dist_zero_right] at H
          exact H.le
        rw [norm_mul, Real.norm_eq_abs (b x), abs_of_nonneg b.nonneg]
        exact (mul_le_mul_of_nonneg_left b.le_one (norm_nonneg _)).trans
          (by simpa only [mul_one] using hψx)
    rw [he]
    exact (hbound χ).trans (mul_le_mul_of_nonneg_left hn hC)
  have hcont : Continuous (fun ε : ℝ => C * ε) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hn : |T ψ| ≤ 0 := ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hsmall ε hε)
  exact abs_eq_zero.mp (le_antisymm hn (abs_nonneg _))

/-- An order-zero residual supported at the origin is a scalar
multiple of evaluation at the origin, on every smooth compact test
(BB Thm 6.3, pp. 251–253). -/
theorem pointSupported_orderZero_eq_eval
    (hΩ : (0 : Fin N → ℝ) ∈ Ω)
    (T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ, |T φ| ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖)
    (haway : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), (0 : Fin N → ℝ) ∉ tsupport (φ : (Fin N → ℝ) → ℝ) → T φ = 0) :
    ∃ α : ℝ, ∀ φ, T φ = α * φ 0 := by
  obtain ⟨η, hs, hc, hd, _, hη⟩ := exists_contDiff_tsupport_subset
    (n := (⊤ : ℕ∞)) (Ω.isOpen.mem_nhds hΩ)
  let χ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨η, hd, hc, hs⟩
  refine ⟨T χ, fun φ => ?_⟩
  have hχ : χ 0 = 1 := hη
  have hz : (φ - φ 0 • χ : TestFunction Ω ℝ (⊤ : ℕ∞)) 0 = 0 := by
    change φ 0 - φ 0 * χ 0 = 0
    rw [hχ, mul_one, sub_self]
  have H := zero_on_test_vanishing_at_origin Ω T hC hbound haway (φ - φ 0 • χ) hz
  rw [map_sub, map_smul] at H
  change T φ - φ 0 * T χ = 0 at H
  nlinarith

end RothschildStein.H1
