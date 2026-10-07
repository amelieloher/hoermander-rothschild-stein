-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.JointModelTransport
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.P1
variable {N : ℕ}

/-- Joint C¹ regularity gives a uniform linear
bound for subtraction at model zero, on compact center sets. -/
theorem exists_compactParameter_model_sub_bound
    {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (ψ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (U ×ˢ (univ : Set (Fin N → ℝ))))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ K, ∀ u, ‖u‖ ≤ R →
      ‖ψ (ξ, u) - ψ (ξ, 0)‖ ≤ M * ‖u‖ := by
  let D := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    (fderiv ℝ ψ p).comp (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ))
  have ho : IsOpen (U ×ˢ (univ : Set (Fin N → ℝ))) := hU.prod isOpen_univ
  have hD : ContinuousOn D (U ×ˢ (univ : Set (Fin N → ℝ))) :=
    (hψ.continuousOn_fderiv_of_isOpen ho le_rfl).clm_comp continuousOn_const
  have hC := hK.prod (isCompact_closedBall (0 : Fin N → ℝ) R)
  obtain ⟨B, hb⟩ := hC.exists_bound_of_continuousOn
    (hD.mono (fun p hp => ⟨hKU hp.1, mem_univ _⟩))
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro ξ hξ u hu
  have hd (v : Fin N → ℝ) : HasFDerivAt (fun y => ψ (ξ, y)) (D (ξ, v)) v := by
    have hp : (ξ, v) ∈ U ×ˢ (univ : Set (Fin N → ℝ)) := ⟨hKU hξ, mem_univ v⟩
    have hj := (hψ.contDiffAt (ho.mem_nhds hp)).differentiableAt (by norm_num)
    exact hj.hasFDerivAt.comp v
      (by simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
        using (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ)).hasFDerivAt.const_add (ξ, 0))
  have hbound (v : Fin N → ℝ) (hv : v ∈ closedBall (0 : Fin N → ℝ) R) :
      ‖fderiv ℝ (fun y => ψ (ξ, y)) v‖ ≤ max B 0 := by
    rw [(hd v).fderiv]
    exact (hb (ξ, v) ⟨hξ, hv⟩).trans (le_max_left _ _)
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => (hd v).differentiableAt) hbound (convex_closedBall (0 : Fin N → ℝ) R)
    (show (0 : Fin N → ℝ) ∈ closedBall 0 R by simpa using hR)
    (show u ∈ closedBall 0 R by simpa using hu)
  simpa using hm

end RothschildStein.P1
