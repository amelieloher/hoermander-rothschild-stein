-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceError
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform first-order Taylor control at every point of a
compact set inside the original open domain. All mean-value segments stay in
that domain (BB Proposition 1.2, p. 3). -/
theorem exists_uniform_taylor_radius
    {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {Z : E → E} (hZ : ContDiffOn ℝ 1 Z Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ ball x δ,
      y ∈ Ω ∧ ‖Z y - Z x - fderiv ℝ Z x (y - x)‖ ≤ ε * ‖y - x‖ := by
  obtain ⟨δ₁, hδ₁, hbuf⟩ := hK.exists_thickening_subset_open hΩ hKΩ
  have hdf : ∀ x ∈ K, ContinuousAt (fderiv ℝ Z) x := by
    intro x hx
    exact (hZ.continuousOn_fderiv_of_isOpen hΩ le_rfl).continuousAt
      (hΩ.mem_nhds (hKΩ hx))
  have hu := hK.uniformContinuousAt_of_continuousAt (fderiv ℝ Z) hdf
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ₂, hδ₂, hd⟩ := Metric.mem_uniformity_dist.mp hu
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hball : ∀ x ∈ K, ball x δ ⊆ Ω := by
    intro x hx y hy
    apply hbuf
    rw [mem_thickening_iff_exists_edist_lt]
    refine ⟨x, hx, ?_⟩
    rw [edist_dist]
    apply (ENNReal.ofReal_lt_ofReal_iff hδ₁).mpr
    exact lt_of_lt_of_le (mem_ball.mp hy) (min_le_left _ _)
  refine ⟨δ, hδ, fun x hx y hy => ⟨hball x hx hy, ?_⟩⟩
  have hder : ∀ z ∈ ball x δ,
      HasFDerivWithinAt (fun w => Z w - fderiv ℝ Z x w)
        (fderiv ℝ Z z - fderiv ℝ Z x) (ball x δ) z := by
    intro z hz
    exact ((hZ.contDiffAt (hΩ.mem_nhds (hball x hx hz))).differentiableAt
      one_ne_zero |>.hasFDerivAt.sub (fderiv ℝ Z x).hasFDerivAt).hasFDerivWithinAt
  have hnorm : ∀ z ∈ ball x δ, ‖fderiv ℝ Z z - fderiv ℝ Z x‖ ≤ ε := by
    intro z hz
    have hh : dist (fderiv ℝ Z x) (fderiv ℝ Z z) < ε := hd (show dist x z < δ₂ from by
      rw [dist_comm]; exact lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)) hx
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hh)
  have hb := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hder hnorm (mem_ball_self hδ) hy
  have heq : (Z y - fderiv ℝ Z x y) - (Z x - fderiv ℝ Z x x) =
      Z y - Z x - fderiv ℝ Z x (y - x) := by rw [map_sub]; abel
  rwa [heq] at hb

/-- The uniform Taylor remainder along a compact trajectory
is little compared with the initial increment, using a uniform Lipschitz
comparison of nearby trajectories (BB Proposition 1.2, p. 3). -/
theorem flow_uniform_linearized_residual
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E} (hZ : ContDiffOn ℝ 1 Z Ω)
    {Φ : E → ℝ → E} {x : E} {a b B : ℝ} (hB : 0 ≤ B)
    (hc : ContinuousOn (Φ x) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, Φ x t ∈ Ω)
    (hLip : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ‖Φ y t - Φ x t‖ ≤ B * ‖y - x‖) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      ‖Z (Φ y t) - Z (Φ x t) - fderiv ℝ Z (Φ x t) (Φ y t - Φ x t)‖ ≤
        ε * ‖y - x‖ := by
  intro ε hε
  have hB1 : 0 < B + 1 := by linarith
  have hK : IsCompact (Φ x '' Icc a b) := isCompact_Icc.image_of_continuousOn hc
  have hKΩ : Φ x '' Icc a b ⊆ Ω := by
    rintro z ⟨t, ht, rfl⟩
    exact hmem t ht
  obtain ⟨δ, hδ, hTaylor⟩ := exists_uniform_taylor_radius hΩ hK hKΩ hZ
    (div_pos hε hB1)
  have hnear : ∀ᶠ y in 𝓝 x, ‖y - x‖ < δ / (B + 1) := by
    filter_upwards [Metric.ball_mem_nhds x (div_pos hδ hB1)] with y hy
    simpa only [mem_ball, dist_eq_norm] using hy
  filter_upwards [hLip, hnear] with y hy hn
  intro t ht
  have hnorm : ‖Φ y t - Φ x t‖ ≤ (B + 1) * ‖y - x‖ := by
    exact (hy t ht).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hball : Φ y t ∈ ball (Φ x t) δ := by
    rw [mem_ball, dist_eq_norm]
    apply lt_of_le_of_lt hnorm
    simpa only [mul_comm] using (lt_div_iff₀ hB1).mp hn
  have hbound := (hTaylor (Φ x t) (mem_image_of_mem _ ht) (Φ y t) hball).2
  calc
    _ ≤ ε / (B + 1) * ‖Φ y t - Φ x t‖ := hbound
    _ ≤ ε / (B + 1) * ((B + 1) * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left hnorm (div_nonneg hε.le hB1.le)
    _ = ε * ‖y - x‖ := by rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hB1)]

end RothschildStein.G1
