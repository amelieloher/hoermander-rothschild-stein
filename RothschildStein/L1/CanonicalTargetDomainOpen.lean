-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CanonicalCommonSourceChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1.CanonicalFrameChartData

/-- The total target domain is open
for common-source canonical charts whose images fit the fixed coefficient
patch. This retains joint smoothness of all remainder coefficients. -/
theorem isOpen_total_target {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hsub : U ⊆ ball x C.radius)
    (hsmall : ∀ η ∈ U, ∀ ξ ∈ U, C.theta (η,ξ) ∈ ball 0 C.radius) :
    IsOpen {z : (Fin N → ℝ) × (Fin N → ℝ) |
      z.1 ∈ U ∧ z.2 ∈ (fun ξ => C.theta (z.1,ξ)) '' U} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨η,u⟩ hz
  change η ∈ U ∧ u ∈ (fun ξ => C.theta (η,ξ)) '' U at hz
  obtain ⟨hη,ξ,hξ,he⟩ := hz
  dsimp only at he
  subst u
  have hp : (η,C.theta (η,ξ)) ∈ ball x C.radius ×ˢ ball 0 C.radius :=
    ⟨hsub hη,hsmall η hη ξ hξ⟩
  have hc := (C.forward_smooth.contDiffAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hp)).continuousAt
  have hm : canonicalFrameMap C.time C.flow (η,C.theta (η,ξ)) ∈ U := by
    rw [C.right_inverse (η,ξ) (C.basePatch_subset ⟨hsub hη,hsub hξ⟩)]
    exact hξ
  have hfst : ContinuousAt (Prod.fst : (Fin N → ℝ) × (Fin N → ℝ) → _) (η,C.theta (η,ξ)) :=
    continuous_fst.continuousAt
  filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hp,
    hfst.preimage_mem_nhds (hU.mem_nhds hη), hc.preimage_mem_nhds (hU.mem_nhds hm)]
    with z hz hzU hzmap
  refine ⟨hzU,canonicalFrameMap C.time C.flow z,hzmap,?_⟩
  exact (C.coefficients z hz).2.2

end RothschildStein.L1.CanonicalFrameChartData
