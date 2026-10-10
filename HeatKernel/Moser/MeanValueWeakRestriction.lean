-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Definitions.IsLocalWeakSolution
import RothschildStein.S.WeakDeriv

/-! # Restricting the local weak equation to smaller cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Restricting both open factors preserves the original weak gradient, local
energy bounds and compactly supported test identity. -/
theorem IsLocalWeakSolution.mono {N q : ℕ}
    {G : HomogeneousGroup N} {hq : q ≤ N} {hqpos : 0 < q}
    {hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1}
    {hspan : bracketSpansOn univ (G.horizontalFields hq)}
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I I' : Opens ℝ} {U U' : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (hI : (I' : Set ℝ) ⊆ (I : Set ℝ))
    (hU : (U' : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ))) :
    IsLocalWeakSolution G hq hqpos hw hspan a I' U' u := by
  obtain ⟨hm, g, hg, henergy, htest⟩ := hu
  refine ⟨hm.mono_measure (Measure.restrict_mono (prod_mono hI hU) le_rfl), g, ?_, ?_, ?_⟩
  · have hg' := hg.filter_mono (ae_mono (Measure.restrict_mono hI le_rfl))
    exact hg'.mono fun _ ht i => S.hasWeakWordDeriv_restrict _ U U' hU (ht i)
  · intro J K hJ hJI hK hKU
    exact henergy J K hJ (hJI.trans hI) hK (hKU.trans hU)
  · intro φ hφ hc hs
    exact htest φ hφ hc (hs.trans (prod_mono hI hU))

end HeatKernel
