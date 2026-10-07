-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceVariationalPackage
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology NNReal

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Locally obtain uniform coefficient and initial-point
Lipschitz bounds from joint continuity of a flow and `C¹` regularity of the
field. Compact buffers keep every Taylor segment inside the original open
domain (BB Proposition 1.2, p. 3). -/
theorem exists_local_flow_bounds
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : E → E} (hZ : ContDiffOn ℝ 1 Z Ω)
    {Φ : E → ℝ → E} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn (fun p : E × ℝ => Φ p.1 p.2) (U ×ˢ Icc (-T) T))
    (hsol : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, HasDerivAt (Φ x) (Z (Φ x t)) t)
    (hinit : ∀ x ∈ U, Φ x 0 = x)
    (hmem : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, Φ x t ∈ Ω)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ ∃ K : ℝ≥0, ∃ B : ℝ, 0 ≤ B ∧
      (∀ x ∈ ball x₀ r, ∀ t ∈ Icc (-T) T, ‖fderiv ℝ Z (Φ x t)‖ ≤ K) ∧
      ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, ∀ t ∈ Icc (-T) T,
        ‖Φ y t - Φ x t‖ ≤ B * ‖y - x‖ := by
  obtain ⟨d, hd, hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  let a := d / 2
  have ha : 0 < a := half_pos hd
  have haU : closedBall x₀ a ⊆ U :=
    (closedBall_subset_ball (half_lt_self hd)).trans hdU
  let D := closedBall x₀ a ×ˢ Icc (-T) T
  let F := fun p : E × ℝ => Φ p.1 p.2
  have hD : IsCompact D := (isCompact_closedBall x₀ a).prod isCompact_Icc
  have hFc : ContinuousOn F D := hc.mono (prod_mono haU Subset.rfl)
  have hFΩ : F '' D ⊆ Ω := by
    rintro _ ⟨p, hp, rfl⟩
    exact hmem p.1 (haU hp.1) p.2 hp.2
  have himage : IsCompact (F '' D) := hD.image_of_continuousOn hFc
  have hdf : ContinuousOn (fderiv ℝ Z) (F '' D) :=
    (hZ.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hFΩ
  obtain ⟨C, hC⟩ := (himage.image_of_continuousOn hdf).isBounded.exists_norm_le
  let K : ℝ≥0 := ⟨|C| + 1, by positivity⟩
  have hK : ∀ p ∈ D, ‖fderiv ℝ Z (F p)‖ ≤ K := by
    intro p hp
    exact (hC _ (mem_image_of_mem _ (mem_image_of_mem _ hp))).trans
      ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
  obtain ⟨δ, hδ, hTaylor⟩ := exists_uniform_taylor_radius hΩ himage hFΩ hZ zero_lt_one
  obtain ⟨ρ, hρ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    (hD.uniformContinuousOn_of_continuous hFc) δ hδ
  let r := min a (ρ / 3)
  have hr : 0 < r := lt_min ha (by positivity)
  have hrA : r ≤ a := min_le_left _ _
  have hrρ : r ≤ ρ / 3 := min_le_right _ _
  have hrU : ball x₀ r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrA)).trans haU
  have hxy : ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, ∀ t ∈ Icc (-T) T,
      dist (Φ y t) (Φ x t) < δ := by
    intro x hx y hy t ht
    have hxD : (x, t) ∈ D := ⟨(ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrA)) hx, ht⟩
    have hyD : (y, t) ∈ D := ⟨(ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrA)) hy, ht⟩
    apply hu (y, t) hyD (x, t) hxD
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    have he := dist_triangle y x₀ x
    have hx' : dist x₀ x < r := by simpa only [dist_comm] using mem_ball.mp hx
    have hy' : dist y x₀ < r := mem_ball.mp hy
    linarith
  have hfield : ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, ∀ t ∈ Icc (-T) T,
      ‖Z (Φ y t) - Z (Φ x t)‖ ≤ ((K : ℝ) + 1) * ‖Φ y t - Φ x t‖ := by
    intro x hx y hy t ht
    have hxD : (x, t) ∈ D := ⟨(ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrA)) hx, ht⟩
    have htay := (hTaylor (Φ x t) (mem_image_of_mem _ hxD) (Φ y t)
      (mem_ball.mpr (hxy x hx y hy t ht))).2
    calc
      _ ≤ ‖Z (Φ y t) - Z (Φ x t) - fderiv ℝ Z (Φ x t) (Φ y t - Φ x t)‖ +
          ‖fderiv ℝ Z (Φ x t) (Φ y t - Φ x t)‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖Φ y t - Φ x t‖ + (K : ℝ) * ‖Φ y t - Φ x t‖ :=
        add_le_add (by simpa only [one_mul] using htay)
          (((fderiv ℝ Z (Φ x t)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hK (x, t) hxD) (norm_nonneg _)))
      _ = ((K : ℝ) + 1) * ‖Φ y t - Φ x t‖ := by ring
  refine ⟨r, hr, hrU, K, Real.exp (((K : ℝ) + 1) * T), (Real.exp_pos _).le,
    fun x hx t ht => hK (x, t) ⟨(ball_subset_closedBall.trans
      (closedBall_subset_closedBall hrA)) hx, ht⟩, ?_⟩
  intro x hx y hy t ht
  have hs : uIcc (0 : ℝ) t ⊆ Icc (-T) T := uIcc_subset_Icc ⟨by linarith, hT.le⟩ ht
  have hdif : ∀ v ∈ uIcc 0 t, HasDerivAt (fun s => Φ y s - Φ x s)
      (Z (Φ y v) - Z (Φ x v)) v :=
    fun v hv => (hsol y (hrU hy) v (hs hv)).sub (hsol x (hrU hx) v (hs hv))
  have he := norm_le_exp_of_deriv_bound_uIcc hdif
    (fun v hv => hfield x hx y hy v (hs hv))
    (show ‖Φ y 0 - Φ x 0‖ ≤ ‖y - x‖ by rw [hinit y (hrU hy), hinit x (hrU hx)])
  have he' : ‖Φ y t - Φ x t‖ ≤ ‖y - x‖ * Real.exp (((K : ℝ) + 1) * T) := by
    apply he.trans
    have habs : |t| ≤ T := abs_le.mpr ht
    gcongr
  simpa only [mul_comm] using he'

end RothschildStein.G1
