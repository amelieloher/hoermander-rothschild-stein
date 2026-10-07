-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1

/-- Swapping both endpoints preserves the exact regular remainder
budget and its compact support inside V × V (BB p. 546). -/
theorem IsRegularKernel.transpose {N : ℕ} {F : KernelFrame N} {m : ℕ}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F m r) :
    IsRegularKernel F m (fun ξ η => r η ξ) := by
  let K := Prod.swap '' tsupport (fun p : (Fin N → ℝ) × (Fin N → ℝ) => r p.1 p.2)
  have hK : IsCompact K := hr.2.1.image continuous_swap
  have hs : Function.support (fun p : (Fin N → ℝ) × (Fin N → ℝ) => r p.2 p.1) ⊆ K := by
    intro p hp
    exact ⟨p.swap, subset_tsupport _ hp, Prod.swap_swap p⟩
  have ht : tsupport (fun p : (Fin N → ℝ) × (Fin N → ℝ) => r p.2 p.1) ⊆ K :=
    closure_minimal hs hK.isClosed
  refine ⟨hr.1.comp (contDiff_snd.prodMk contDiff_fst),
    hK.of_isClosed_subset (isClosed_tsupport _) ht, ?_⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := ht hp
  exact ⟨(hr.2.2 hq).2, (hr.2.2 hq).1⟩

end RothschildStein.P1
