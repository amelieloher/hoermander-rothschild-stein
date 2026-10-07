-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- A jointly smooth function zero on the parameter axis has a uniform
linear remainder bound on a smaller closed parameter/coefficient patch. -/
theorem compact_parameter_zero_bound {N : ℕ} (x : Fin N → ℝ) {r : ℝ} (hr : 0 < r)
    (F : ((Fin N → ℝ) × (Fin N → ℝ)) → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (ball x r ×ˢ ball 0 r))
    (hF0 : ∀ η ∈ ball x r, F (η,0) = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ η ∈ closedBall x (r/2), ∀ u ∈ closedBall 0 (r/2),
      |F (η,u)| ≤ B * ‖u‖ := by
  let K := closedBall x (r/2) ×ˢ closedBall (0 : Fin N → ℝ) (r/2)
  have hK : IsCompact K := (isCompact_closedBall x (r/2)).prod (isCompact_closedBall 0 (r/2))
  have hsub : K ⊆ ball x r ×ˢ ball 0 r := by
    intro q hq
    exact ⟨(closedBall_subset_ball (by linarith : r/2 < r)) hq.1,
      (closedBall_subset_ball (by linarith : r/2 < r)) hq.2⟩
  have hc := (hF.fderiv_of_isOpen (m := (⊤ : ℕ∞)) (isOpen_ball.prod isOpen_ball) (by simp)).continuousOn.mono hsub
  obtain ⟨b,hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨max 1 b, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro η hη u hu
  have hη0 : (η,(0 : Fin N → ℝ)) ∈ K :=
    ⟨hη, mem_closedBall_self (by linarith)⟩
  have hηu : (η,u) ∈ K := ⟨hη,hu⟩
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := F) (s := K) (C := max 1 b)
    (fun q hq => (hF.contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds (hsub hq))).differentiableAt (by simp))
    (fun q hq => (hb _ (mem_image_of_mem _ hq)).trans (le_max_right 1 b))
    ((convex_closedBall x (r/2)).prod (convex_closedBall (0 : Fin N → ℝ) (r/2))) hη0 hηu
  rw [hF0 η (hsub hη0).1, sub_zero] at hh
  simpa only [Real.norm_eq_abs, Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def,
    norm_zero, max_eq_right (norm_nonneg u)] using hh
end RothschildStein.L1
