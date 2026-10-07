-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FlowJacobianDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.S
variable {n : ℕ}

/-- The flow's actual spatial differential is jointly
continuous on the open flow domain (BB (2.28), pp. 89–90). -/
theorem continuousOn_flow_spatial_fderiv
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {τ : ℝ}
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ)) :
    ContinuousOn (fun p => fderiv ℝ (fun y => Φ (y,p.2)) p.1) (U ×ˢ Ioo (-τ) τ) := by
  let i : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) × ℝ) := ContinuousLinearMap.inl ℝ _ ℝ
  have hJ : ∀ p ∈ U ×ˢ Ioo (-τ) τ,
      fderiv ℝ (fun y => Φ (y,p.2)) p.1 = (fderiv ℝ Φ p).comp i := by
    intro p hp
    exact (((hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)).fderiv
  intro p hp
  have hs := hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp)
  have hD := (hs.fderiv_right (m := 0) (by simp)).continuousAt
  have hc : ContinuousAt (fun q => (fderiv ℝ Φ q).comp i) p :=
    hD.clm_comp continuousAt_const
  have he : (fun q => fderiv ℝ (fun y => Φ (y,q.2)) q.1) =ᶠ[𝓝 p]
      (fun q => (fderiv ℝ Φ q).comp i) := by
    filter_upwards [(hU.prod isOpen_Ioo).mem_nhds hp] with q hq
    exact hJ q hq
  exact (hc.congr_of_eventuallyEq he).continuousWithinAt

/-- The change-of-variables determinant is jointly
continuous, so it is bounded on the compact flow buffer (BB p. 90). -/
theorem continuousOn_flow_jacobian
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {τ : ℝ}
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ)) :
    ContinuousOn (fun p => (fderiv ℝ (fun y => Φ (y,p.2)) p.1).det)
      (U ×ˢ Ioo (-τ) τ) :=
  ContinuousLinearMap.continuous_det.comp_continuousOn
    (continuousOn_flow_spatial_fderiv hU Φ hjoint)

/-- The coordinate divergence is continuous
on every open smoothness domain (BB pp. 89–90). -/
theorem continuousOn_smooth_field_divergence
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) :
    ContinuousOn (Hormander.Interface.euclideanDivergence X) Ω := by
  unfold Hormander.Interface.euclideanDivergence
  apply continuousOn_finsetSum
  intro i _ x hx
  have hD := ((hX.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 0) (by simp)).continuousAt
  exact ((continuous_apply i).continuousAt.comp
    (hD.clm_apply (continuousAt_const (y := Hormander.Interface.basisVec i)))).continuousWithinAt

end RothschildStein.S
