-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompactLocalMeasurability
public import HeatKernel.Form.ParabolicEnergyCurves
import Mathlib.Tactic.Linter

/-! # Joint measurability of local parabolic weak gradients -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Compact-cylinder energy bounds imply joint almost everywhere strong measurability
of every gradient component on the entire open space-time cylinder. -/
theorem HasLocalParabolicEnergyBounds.aestronglyMeasurable_gradient {N q : ℕ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hb : HasLocalParabolicEnergyBounds I U u g) (i : Fin q) :
    AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2)
      (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))) := by
  apply aestronglyMeasurable_restrict_open_of_memLp_compacts volume
    ⟨(I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)), I.isOpen.prod U.isOpen⟩
  intro S hS hSU
  have hJ : IsCompact (Prod.fst '' S) := hS.image continuous_fst
  have hK : IsCompact (Prod.snd '' S) := hS.image continuous_snd
  have hJI : Prod.fst '' S ⊆ (I : Set ℝ) := by
    rintro t ⟨z, hz, rfl⟩
    exact (hSU hz).1
  have hKU : Prod.snd '' S ⊆ (U : Set (Fin N → ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    exact (hSU hz).2
  have hrect : S ⊆ (Prod.fst '' S) ×ˢ (Prod.snd '' S) := by
    intro z hz
    exact ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  exact MemLp.mono_measure (Measure.restrict_mono hrect le_rfl)
    ((hb _ _ hJ hJI hK hKU).2 i)

end HeatKernel
