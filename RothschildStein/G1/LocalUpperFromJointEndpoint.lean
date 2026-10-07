-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.JointChartDerivativeBounds
public import RothschildStein.G1.ControlUpperFromChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RothschildStein.G1

/-- Joint C¹ endpoint regularity and actual parameter costs
give upper-comparison constants uniform over nearby centers.
No derivative bound or inverse-function radius is assumed separately
(BB Theorem 1.53, p. 35). -/
theorem exists_local_control_upper_of_joint_endpoint {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (F : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    (z : Fin n → ℝ) (hF : ContDiffAt ℝ 1 F (0, z))
    (hzero : ∀ x, F (0, x) = x)
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hAeq : (fderiv ℝ F (0, z)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) = (A : _ →L[ℝ] _))
    {L α : ℝ} (hL : 0 < L) (hα : 0 ≤ α)
    (hcost : ∀ᶠ q : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (0, z),
      controlDistance Ω w X q.2 (F q) ≤ ENNReal.ofReal (L * ‖q.1‖ ^ α)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ x ∈ ball z ρ, ∀ y : Fin n → ℝ,
      ‖y - x‖ < ρ → controlDistance Ω w X x y ≤ ENNReal.ofReal (C * ‖y - x‖ ^ α) := by
  let P : ℝ := max 1 ‖(A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖
  have hP : 0 < P := zero_lt_one.trans_le (le_max_left _ _)
  have hAP : ‖(A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ P := le_max_right _ _
  obtain ⟨δ, hδ, hD⟩ := exists_joint_chart_derivative_neighborhood F z hF
    (show 0 < 1 / (2 * P) by positivity)
  obtain ⟨ε, hε, hcostε⟩ := Metric.mem_nhds_iff.mp hcost
  let r : ℝ := min δ ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r ≤ δ := by dsimp [r]; linarith [min_le_left δ ε]
  have hrε : r ≤ ε := by dsimp [r]; linarith [min_le_right δ ε]
  let ρ : ℝ := min r (r / (4 * P))
  refine ⟨ρ, L * (2 * P) ^ α, lt_min hr (by positivity),
    mul_pos hL (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro x hx y hy
  have hxr : x ∈ ball z r := (ball_subset_ball (min_le_left r (r / (4 * P)))) hx
  let f := fun u : Fin n → ℝ => F (u, x)
  let D := fun u : Fin n → ℝ => (fderiv ℝ F (u, x)).comp
    (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))
  have hd : ∀ u ∈ ball 0 r, HasFDerivAt f (D u) u := fun u hu =>
    (hD u (hu.trans_le hrδ) x (hxr.trans_le hrδ)).1
  have hb : ∀ u ∈ ball 0 r, ‖D u - (A : _ →L[ℝ] _)‖ ≤ 1 / (2 * P) := by
    intro u hu
    simpa only [D, hAeq] using (hD u (hu.trans_le hrδ) x (hxr.trans_le hrδ)).2.le
  have hc : ∀ u ∈ ball 0 r, controlDistance Ω w X (f 0) (f u) ≤
      ENNReal.ofReal (L * ‖u‖ ^ α) := by
    intro u hu
    have hq : (u, x) ∈ ball (0, z) ε := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt (hu.trans_le hrε) (hxr.trans_le hrε)
    simpa only [mem_ofPred_eq, f, hzero] using hcostε hq
  have hyF : ‖y - f 0‖ ≤ r / (4 * P) := by
    simpa only [f, hzero] using hy.le.trans (min_le_right r (r / (4 * P)))
  have hh := controlDistance_upper_of_endpoint_chart Ω w X f D A hr hP hL.le hα
    hAP hd hb hc hyF
  simpa only [f, hzero] using hh

end RothschildStein.G1
