-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CoefficientEndpointIntegral

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- The original coefficient derivative agrees with its actual
endpoint integral on one parameter/initial-point neighborhood. The common
forward-trajectory buffer is derived from compactness (BB pp. 441–443). -/
theorem linear_field_flow_coefficient_endpoint_integral_eventuallyEq {m N : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin N → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (∑ j, p.1 j • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {z : Fin m → ℝ} (hz : z ∈ A) {x : Fin N → ℝ} (hx : x ∈ U)
    (hforward : ∀ s ∈ Icc (0 : ℝ) 1, Φ ((z, x), s) ∈ U) (i : Fin m) :
    (fun p => fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1)) =ᶠ[𝓝 (z, x)]
    (fun p => ∫ s in (0 : ℝ)..1,
      fderiv ℝ (fun y => Φ ((p.1, y), s)) (Φ ((p.1, Φ (p, 1)), -s))
        (W i (Φ ((p.1, Φ (p, 1)), -s)))) := by
  let S := ((A ×ˢ U) ×ˢ Ioo (-τ) τ) ∩ Φ ⁻¹' U
  have hS : IsOpen S := hc.isOpen_inter_preimage ((hA.prod hU).prod isOpen_Ioo) hU
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, ((z, x), s) ∈ S := fun s hs =>
    ⟨⟨⟨hz, hx⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩, hforward s hs⟩
  have he : ∀ᶠ p in 𝓝 (z, x), ∀ s ∈ Icc (0 : ℝ) 1, (p, s) ∈ S :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun s hs => hS.mem_nhds (hseg s hs))
  filter_upwards [he] with p hp
  have hstart := hp 0 (by simp)
  exact linear_field_flow_coefficient_endpoint_integral hA hΩ hU hUΩ W hW hτ Φ hc hΦ
    hstart.1.1.1 hstart.1.1.2 (fun s hs => (hp s hs).2) i

end RothschildStein.G4
