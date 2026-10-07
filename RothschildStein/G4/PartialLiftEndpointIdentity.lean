-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedPartialLiftExtension
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- The actual lift identity persists at the constructed maximal
endpoint. Only continuity at the endpoint is used; no global chart
inverse or covering hypothesis is required (BB Prop 9.52, p. 449). -/
theorem partialLift_endpoint_identity {n : ℕ} {T : ℝ} (hT : 0 < T)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (Θ γ : ℝ → (Fin n → ℝ))
    (hΘ : ContinuousAt Θ T) (hF : ContinuousAt F (Θ T))
    (hγ : ContinuousWithinAt γ (Icc (0 : ℝ) T) T)
    (hlift : ∀ s ∈ Ico (0 : ℝ) T, F (Θ s) = γ s) :
    F (Θ T) = γ T := by
  let endpointNhdsWithinNeBot : NeBot (𝓝[Ico (0 : ℝ) T] T) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ico hT.ne]
      exact ⟨hT.le, le_rfl⟩)
  have heq : (fun s => F (Θ s)) =ᶠ[𝓝[Ico (0 : ℝ) T] T] γ :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hlift s hs)
  exact tendsto_nhds_unique ((hF.comp hΘ).continuousWithinAt.tendsto)
    ((hγ.mono Ico_subset_Icc_self).tendsto.congr' heq.symm)

end RothschildStein.G4
