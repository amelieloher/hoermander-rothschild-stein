-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlows

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Local uniqueness uses the actual smooth field near the common initial
point, without a global Lipschitz hypothesis (BB Prop 1.2, p. 3). -/
theorem integralCurve_eventuallyEq {N : ℕ} {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    {α β : ℝ → (Fin N → ℝ)} {t₀ : ℝ}
    (hZ : ContDiffAt ℝ 1 Z (α t₀))
    (hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (Z (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (Z (β t)) t)
    (heq : α t₀ = β t₀) : α =ᶠ[𝓝 t₀] β := by
  obtain ⟨L, U, hU, hLip⟩ := hZ.exists_lipschitzOnWith
  have ha := (hα.self_of_nhds).continuousAt.preimage_mem_nhds hU
  have hb := (hβ.self_of_nhds).continuousAt.preimage_mem_nhds (by rwa [← heq])
  exact ODE_solution_unique_of_eventually (v := fun _ => Z) (s := fun _ => U)
    (Eventually.of_forall (fun _ => hLip)) (hα.and ha) (hβ.and hb) heq

/-- Uniqueness on an entire open time interval for curves staying in the
original open spatial domain (BB Prop 1.2, p. 3). -/
theorem integralCurve_eqOn {N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {Z : (Fin N → ℝ) → (Fin N → ℝ)} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {α β : ℝ → (Fin N → ℝ)} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (Z (α t)) t ∧ α t ∈ Ω)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (Z (β t)) t ∧ β t ∈ Ω)
    (heq : α t₀ = β t₀) : EqOn α β (Ioo a b) := by
  let S := {t | α t = β t} ∩ Ioo a b
  suffices hsub : Ioo a b ⊆ S from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := S) _
    ⟨t₀, ⟨ht₀, ⟨heq, ht₀⟩⟩⟩
  · change closure ({t | α t = β t} ∩ Ioo a b) ∩ Ioo a b ⊆ {t | α t = β t} ∩ Ioo a b
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hα t ht).1.continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hβ t ht).1.continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem : ∀ᶠ v in 𝓝 t, v ∈ Ioo a b := Ioo_mem_nhds ht.2.1 ht.2.2
    have hZa : ContDiffAt ℝ 1 Z (α t) :=
      (hZ.contDiffAt (hΩ.mem_nhds (hα t ht.2).2)).of_le (by simp)
    have hae : ∀ᶠ v in 𝓝 t, HasDerivAt α (Z (α v)) v :=
      hmem.mono (fun v hv => (hα v hv).1)
    have hbe : ∀ᶠ v in 𝓝 t, HasDerivAt β (Z (β v)) v :=
      hmem.mono (fun v hv => (hβ v hv).1)
    exact ((integralCurve_eventuallyEq hZa hae hbe ht.1).and hmem).mono (fun _ h => h)

end RothschildStein.G1
