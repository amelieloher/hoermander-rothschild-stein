-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.JointChartInverse
public import RothschildStein.P1.RightParametrixTransport
public import RothschildStein.P1.SingularSplitRadius
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The actual inverse chart displaces its center
by O(‖u‖), uniformly on compact center sets and a fixed model ball. -/
theorem exists_inverse_zero_bound
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ ξ ∈ K, ∀ u, ‖u‖ ≤ ρ →
      u ∈ (C.e ξ).target ∧ ‖(C.e ξ).symm u - ξ‖ ≤ M * ‖u‖ := by
  obtain ⟨R, hR, htarget⟩ := C.exists_ball_subset_e_target hK hKU
  let ρ := R / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hsub : K ×ˢ closedBall (0 : Fin (n + m) → ℝ) ρ ⊆ C.T := by
    intro p hp
    refine ⟨hKU hp.1, htarget p.1 hp.1 p.2 ?_⟩
    have hn : ‖p.2‖ ≤ ρ := by simpa using hp.2
    have hρR : ρ < R := by dsimp [ρ]; linarith
    exact hn.trans_lt hρR
  let I := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.e p.1).symm p.2
  let D := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
    (fderiv ℝ I p).comp
      (ContinuousLinearMap.inr ℝ (Fin (n + m) → ℝ) (Fin (n + m) → ℝ))
  have hD : ContinuousOn D C.T :=
    (C.inverse_joint_contDiffOn.continuousOn_fderiv_of_isOpen C.isOpen_T (by simp)).clm_comp
      continuousOn_const
  obtain ⟨B, hb⟩ := (hK.prod (isCompact_closedBall (0 : Fin (n + m) → ℝ) ρ)).exists_bound_of_continuousOn
    (hD.mono hsub)
  refine ⟨ρ, max B 0, hρ, le_max_right _ _, ?_⟩
  intro ξ hξ u hu
  have huB : u ∈ closedBall (0 : Fin (n + m) → ℝ) ρ := by simpa using hu
  have hd (v : Fin (n + m) → ℝ) (hv : v ∈ closedBall (0 : Fin (n + m) → ℝ) ρ) :
      HasFDerivAt (fun y => (C.e ξ).symm y) (D (ξ, v)) v := by
    have hj := (C.inverse_joint_contDiffOn.contDiffAt
      (C.isOpen_T.mem_nhds (hsub (show (ξ, v) ∈ K ×ˢ closedBall 0 ρ from ⟨hξ, hv⟩)))).differentiableAt (by simp)
    exact hj.hasFDerivAt.comp v
      (by simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
        using (ContinuousLinearMap.inr ℝ (Fin (n + m) → ℝ) (Fin (n + m) → ℝ)).hasFDerivAt.const_add (ξ, 0))
  have hbound (v : Fin (n + m) → ℝ) (hv : v ∈ closedBall (0 : Fin (n + m) → ℝ) ρ) :
      ‖fderiv ℝ (fun y => (C.e ξ).symm y) v‖ ≤ max B 0 := by
    rw [(hd v hv).fderiv]
    exact (hb (ξ, v) ⟨hξ, hv⟩).trans (le_max_left _ _)
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun v hv => (hd v hv).differentiableAt) hbound
    (convex_closedBall (0 : Fin (n + m) → ℝ) ρ)
    (show (0 : Fin (n + m) → ℝ) ∈ closedBall 0 ρ by simpa using hρ.le) huB
  refine ⟨(hsub (show (ξ, u) ∈ K ×ˢ closedBall 0 ρ from ⟨hξ, huB⟩)).2, ?_⟩
  simpa only [symm_zero (hKU hξ), sub_zero] using hm

end RothschildStein.P1.LiftedChart
