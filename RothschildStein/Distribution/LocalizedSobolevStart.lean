-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedFiniteOrder
public import RothschildStein.Distribution.FiniteSchwartzOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open SchwartzMap
open scoped BigOperators
namespace RothschildStein.Distribution

/-- finite derivative order is preserved
under the Schwartz transport from `Fin N → ℝ` to the Euclidean carrier. -/
theorem schwartzToCoordinates_seminorm_le {N : ℕ} (n : ℕ)
    (φ : SchwartzMap (Hormander.A.Carrier N) ℂ) :
    SchwartzMap.seminorm ℂ 0 n (Hormander.F.schwartzToCoordinatesCLM N φ) ≤
      ‖(Hormander.F.coordinateEquiv N).toContinuousLinearMap‖ ^ n *
        SchwartzMap.seminorm ℂ 0 n φ := by
  apply SchwartzMap.seminorm_le_bound ℂ 0 n _ (by positivity)
  intro x
  simp only [pow_zero, one_mul]
  change ‖iteratedFDeriv ℝ n (φ ∘ (Hormander.F.coordinateEquiv N).toContinuousLinearMap) x‖ ≤ _
  rw [(Hormander.F.coordinateEquiv N).toContinuousLinearMap.iteratedFDeriv_comp_right
    (φ.smooth (⊤ : ℕ∞)) x (by simp)]
  have h := (iteratedFDeriv ℝ n φ (Hormander.F.coordinateEquiv N x)).norm_compContinuousLinearMap_le
    (fun _ => (Hormander.F.coordinateEquiv N).toContinuousLinearMap)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ n _) (by positivity))

/-- Every cutoff of a distribution belongs to a negative-order Sobolev
space on Euclidean space. -/
theorem localizedTemperedEuclidean_memSobolev_neg
    {N : ℕ} (U : TopologicalSpace.Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞)) :
    ∃ m : ℕ, ∀ s : ℝ, (N : ℝ) < 2 * s →
      TemperedDistribution.MemSobolev (-((m : ℝ) + s)) 2
        (localizedTemperedEuclidean U χ T) := by
  obtain ⟨m, C, hC, h⟩ := localizedTempered_finiteSchwartzOrder U χ T
  let D : ℝ := max 1 ‖(Hormander.F.coordinateEquiv N).toContinuousLinearMap‖
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  refine ⟨m, fun s hs => ?_⟩
  apply memSobolev_neg_of_finiteSchwartzOrder m s hs
    (localizedTemperedEuclidean U χ T) (C := C * D ^ m) (by positivity)
  intro φ
  have hn (n : ℕ) (hn : n ≤ m) :
      SchwartzMap.seminorm ℂ 0 n (Hormander.F.schwartzToCoordinatesCLM N φ) ≤
      D ^ m * SchwartzMap.seminorm ℂ 0 n φ := by
    apply (schwartzToCoordinates_seminorm_le n φ).trans
    apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) n).trans
      (pow_le_pow_right₀ hD hn)
  have hb := h (Hormander.F.schwartzToCoordinatesCLM N φ)
  change ‖localizedTempered U χ T (Hormander.F.schwartzToCoordinatesCLM N φ)‖ ≤ _
  calc
    _ ≤ C * ∑ n ∈ Finset.range (m + 1),
        SchwartzMap.seminorm ℂ 0 n (Hormander.F.schwartzToCoordinatesCLM N φ) := hb
    _ ≤ C * ∑ n ∈ Finset.range (m + 1), D ^ m * SchwartzMap.seminorm ℂ 0 n φ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro n hn'
      exact hn n (Finset.mem_range_succ_iff.mp hn')
    _ = _ := by rw [← Finset.mul_sum]; ring

end RothschildStein.Distribution
