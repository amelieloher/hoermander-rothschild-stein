-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SupportedRegularity
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function
open scoped Topology

namespace RothschildStein.G4

/-- A locally smooth function has a globally smooth representative
agreeing on an open neighborhood of any compact subset of its actual domain.
The cutoff is auxiliary and leaves the local integrand unchanged
(BB pp. 441–443, common-buffer step). -/
theorem exists_contDiff_extension_near_compact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S K : Set E} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {G : E → F} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) :
    ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ EqOn g G V := by
  obtain ⟨T, hT, hKT, hTS⟩ := hK.exists_isOpen_closure_subset (hS.mem_nhdsSet.mpr hKS)
  obtain ⟨V, hV, hKV, hVT⟩ := hK.exists_isOpen_closure_subset (hT.mem_nhdsSet.mpr hKT)
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hT isClosed_closure hVT
  let g : E → F := fun x => χ x • G x
  have hsupp : tsupport g ⊆ S := by
    apply (tsupport_smul_subset_left χ G).trans
    change closure (support χ) ⊆ S
    rw [hχsupp]
    exact hTS
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    RothschildStein.G1.contDiff_of_supported_contDiffOn hS (hχ.contDiffOn.smul hG) hsupp
  refine ⟨g, hg, V, hV, hKV, ?_⟩
  intro x hx
  simp only [g, (hχone x).mp (subset_closure hx), one_smul]

end RothschildStein.G4
