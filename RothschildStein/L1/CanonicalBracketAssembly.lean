-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartLocalInverse
public import RothschildStein.L1.PushforwardBracket
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- The actual vector field pushed into the canonical chart. -/
def pullbackField (D : CanonicalFrameChartData Ω Y x) (η : Fin N → ℝ)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (u : Fin N → ℝ) : Fin N → ℝ :=
  fderiv ℝ (fun ξ => D.theta (η,ξ)) (canonicalFrameMap D.time D.flow (η,u))
    (V (canonicalFrameMap D.time D.flow (η,u)))

/-- Actual pulled-back fields are smooth at the inverse coordinates. -/
theorem pullbackField_contDiffAt (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiffAt ℝ (⊤ : ℕ∞) V ξ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (D.pullbackField η V) (D.theta (η,ξ)) := by
  have hK := D.forward_at_inverse_contDiffAt_of_mem η ξ hq
  have he := D.right_inverse (η,ξ) hq
  have hθ := (D.theta_right_contDiffAt_of_mem η ξ hq).fderiv_right
    (m := (⊤ : ℕ∞)) (by simp)
  have hθ' : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z => D.theta (η,z)))
      (canonicalFrameMap D.time D.flow (η,D.theta (η,ξ))) := by rwa [he]
  have hV' : ContDiffAt ℝ (⊤ : ℕ∞) V
      (canonicalFrameMap D.time D.flow (η,D.theta (η,ξ))) := by rwa [he]
  exact (hθ'.comp (D.theta (η,ξ)) (f := fun u => canonicalFrameMap D.time D.flow (η,u)) hK).clm_apply
    (hV'.comp (D.theta (η,ξ)) (f := fun u => canonicalFrameMap D.time D.flow (η,u)) hK)

/-- The coordinate pushforward relation holds on an actual neighborhood. -/
theorem pullbackField_relation_eventually (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) :
    (fun z => fderiv ℝ (fun w => D.theta (η,w)) z (V z)) =ᶠ[𝓝 ξ]
      (fun z => D.pullbackField η V (D.theta (η,z))) := by
  have hc : ContinuousAt (fun z : Fin N → ℝ => (η,z)) ξ :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards [hc.preimage_mem_nhds (D.inverseDomain_open.mem_nhds hq)] with z hz
  simp only [pullbackField,D.right_inverse (η,z) hz]

/-- The actual constructed charts preserve
brackets throughout their open joint domain (BB Proposition 10.22). -/
theorem pullbackField_lieBracket (D : CanonicalFrameChartData Ω Y x)
    (η ξ : Fin N → ℝ) (hq : (η,ξ) ∈ D.inverseDomain)
    (V W : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffAt ℝ (⊤ : ℕ∞) V ξ) (hW : ContDiffAt ℝ (⊤ : ℕ∞) W ξ) :
    D.pullbackField η (VectorField.lieBracket ℝ V W) (D.theta (η,ξ)) =
      VectorField.lieBracket ℝ (D.pullbackField η V) (D.pullbackField η W) (D.theta (η,ξ)) := by
  have he := lieBracket_pushforward (fun z => D.theta (η,z)) ξ
    (D.theta_right_contDiffAt_of_mem η ξ hq) V W (D.pullbackField η V) (D.pullbackField η W)
    (hV.differentiableAt (by simp)) (hW.differentiableAt (by simp))
    ((D.pullbackField_contDiffAt η ξ hq V hV).differentiableAt (by simp))
    ((D.pullbackField_contDiffAt η ξ hq W hW).differentiableAt (by simp))
    (D.pullbackField_relation_eventually η ξ hq V) (D.pullbackField_relation_eventually η ξ hq W)
  simpa only [pullbackField,D.right_inverse (η,ξ) hq] using he
end CanonicalFrameChartData
end RothschildStein.L1
