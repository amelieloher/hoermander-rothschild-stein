-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedLiftMargin
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.DenselyOrdered

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G4

/-- Weighted Lipschitz bounds extend an actual partial lift to its
maximal endpoint, retaining every coordinate bound. The extension is
constructed from the partial lift, rather than assumed from compactness
(BB Prop 9.52, continuation argument, p. 449). -/
theorem weighted_partialLift_extend_endpoint {n : ℕ} (w : Fin n → ℕ+)
    {r T C b : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hCb : 0 ≤ C * b) (θ : ℝ → (Fin n → ℝ)) (hθ0 : θ 0 = 0)
    (hvariation : ∀ σ ∈ Ico (0 : ℝ) T, ∀ τ ∈ Ico (0 : ℝ) T, ∀ i,
      |θ τ i - θ σ i| ≤ C * b * r ^ (w i : ℕ) * |τ - σ|) :
    ∃ Θ : ℝ → (Fin n → ℝ), LipschitzWith ⟨C * b, hCb⟩ Θ ∧
      EqOn θ Θ (Ico (0 : ℝ) T) ∧
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ i, |Θ τ i| ≤ C * b * r ^ (w i : ℕ) := by
  have hLip : LipschitzOnWith ⟨C * b, hCb⟩ θ (Ico (0 : ℝ) T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro σ hσ τ hτ
    apply (dist_pi_le_iff (mul_nonneg hCb dist_nonneg)).mpr
    intro i
    have hp : r ^ (w i : ℕ) ≤ 1 := pow_le_one₀ hr.le hr1
    have hh := hvariation τ hτ σ hσ i
    rw [Real.dist_eq, Real.dist_eq]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hCb hp) (abs_nonneg _))
  obtain ⟨Θ, hΘ, heq⟩ := hLip.extend_pi
  refine ⟨Θ, hΘ, heq, ?_⟩
  intro τ hτ i
  have hclosed : IsClosed {t : ℝ | |Θ t i| ≤ C * b * r ^ (w i : ℕ)} :=
    isClosed_le ((continuous_apply i).comp hΘ.continuous |>.abs) continuous_const
  have hbound : Ico (0 : ℝ) T ⊆ {t : ℝ | |Θ t i| ≤ C * b * r ^ (w i : ℕ)} := by
    intro t ht
    have hh := hvariation 0 ⟨le_rfl, hT⟩ t ht i
    rw [hθ0, Pi.zero_apply, sub_zero, sub_zero, abs_of_nonneg ht.1] at hh
    change |Θ t i| ≤ C * b * r ^ (w i : ℕ)
    rw [← heq ht]
    exact hh.trans (mul_le_of_le_one_right (mul_nonneg hCb (pow_nonneg hr.le _))
      (ht.2.le.trans hT1))
  apply closure_minimal hbound hclosed
  rwa [closure_Ico hT.ne]

/-- The constructed endpoint extension stays strictly in the
half-box under the numerical weighted margin, so a local inverse there
can continue the lift (BB Prop 9.52, p. 449). -/
theorem weighted_partialLift_extend_halfBox {n s : ℕ} (w : Fin n → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) {r T a C b : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (hCb : 0 ≤ C * b)
    (hmargin : C * b < (a / 2) ^ s / 4)
    (θ : ℝ → (Fin n → ℝ)) (hθ0 : θ 0 = 0)
    (hvariation : ∀ σ ∈ Ico (0 : ℝ) T, ∀ τ ∈ Ico (0 : ℝ) T, ∀ i,
      |θ τ i - θ σ i| ≤ C * b * r ^ (w i : ℕ) * |τ - σ|) :
    ∃ Θ : ℝ → (Fin n → ℝ), LipschitzWith ⟨C * b, hCb⟩ Θ ∧
      EqOn θ Θ (Ico (0 : ℝ) T) ∧
      ∀ τ ∈ Icc (0 : ℝ) T, Θ τ ∈ weightedBox w (a * r / 2) := by
  obtain ⟨Θ, hΘ, heq, hbound⟩ := weighted_partialLift_extend_endpoint w hr hr1 hT hT1 hCb θ hθ0 hvariation
  exact ⟨Θ, hΘ, heq, fun τ hτ => weighted_lift_mem_halfBox w hw ha ha1 hr hmargin
    (Θ τ) (hbound τ hτ)⟩

end RothschildStein.G4
