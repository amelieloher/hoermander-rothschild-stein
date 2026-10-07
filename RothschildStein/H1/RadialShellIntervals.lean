-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellGeometry
public import RothschildStein.H1.ShellCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A cancelled shell has zero signed mass on every gauge interval.
This supplies an interval test for radial weighting. -/
theorem integral_shellIndicator_gaugeInterval_zero
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (he : HasVanishingShellIntegrals ν f)
    {r R : ℝ} (hr : 0 < r) (a b : ℝ) :
    ∫ x in ν ⁻¹' Icc a b, (gaugeShell ν r R).indicator f x = 0 := by
  have hS := measurableSet_gaugeShell hν r R
  rw [setIntegral_indicator hS]
  have hset : (ν ⁻¹' Icc a b) ∩ gaugeShell ν r R =
      gaugeShell ν (max r a) (min R b) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Icc, gaugeShell, mem_ofPred_eq,
      max_le_iff, le_min_iff]
    tauto
  rw [hset]
  have hl : 0 < max r a := hr.trans_le (le_max_left r a)
  by_cases hlt : max r a < min R b
  · exact he _ _ hl hlt
  · have hn : volume (gaugeShell ν (max r a) (min R b)) = 0 := by
      by_cases heq : max r a = min R b
      · have hs : gaugeShell ν (max r a) (min R b) = {x | ν x = max r a} := by
          rw [← heq]
          ext x
          simp only [gaugeShell, mem_ofPred_eq]
          exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
        rw [hs]
        exact volume_gauge_level G hν hl
      · have hs : gaugeShell ν (max r a) (min R b) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact heq (le_antisymm (le_trans hx.1 hx.2) (le_of_not_gt hlt))
        rw [hs, measure_empty]
    rw [Measure.restrict_eq_zero.mpr hn, integral_zero_measure]

end RothschildStein.H1
