-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CoefficientEndpointAgreement

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- A compact forward trajectory in an open initial-point buffer
supplies a common nearby parameter/initial-point buffer for the whole
segment (BB Lemma 9.48, pp. 441–443). -/
theorem parameterFlow_forward_segment_eventually {P E : Type*}
    [TopologicalSpace P] [TopologicalSpace E]
    {V : Set P} {U : Set E} (hV : IsOpen V) (hU : IsOpen U)
    {τ : ℝ} (hτ : 1 < τ) (Φ : P × ℝ → E)
    (hc : ContinuousOn Φ (V ×ˢ Ioo (-τ) τ)) {p : P} (hp : p ∈ V)
    (hforward : ∀ t ∈ Icc (0 : ℝ) 1, Φ (p, t) ∈ U) :
    ∀ᶠ q in 𝓝 p, q ∈ V ∧ ∀ t ∈ Icc (0 : ℝ) 1, Φ (q, t) ∈ U := by
  let S := (V ×ˢ Ioo (-τ) τ) ∩ Φ ⁻¹' U
  have hS : IsOpen S := hc.isOpen_inter_preimage (hV.prod isOpen_Ioo) hU
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (p, t) ∈ S := fun t ht =>
    ⟨⟨hp, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hforward t ht⟩
  have he : ∀ᶠ q in 𝓝 p, ∀ t ∈ Icc (0 : ℝ) 1, (q, t) ∈ S :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun t ht => hS.mem_nhds (hseg t ht))
  filter_upwards [he] with q hq
  exact ⟨(hq 0 (by simp)).1.1, fun t ht => (hq t ht).2⟩

end RothschildStein.G4
