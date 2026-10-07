-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellDefs
public import RothschildStein.G2.MeasureConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive gauge level sets have zero volume; no smooth gauge
surface or surface measure is required (BB p. 274). -/
theorem volume_gauge_level {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {r : ℝ} (hr : 0 < r) : volume {x : Fin N → ℝ | ν x = r} = 0 := by
  simpa only [G2.gaugeDistance, G2.inv_zero, G2.zero_mul] using
    G2.volume_gaugeSphere hν (0 : Fin N → ℝ) hr

/-- Almost every point avoids each prescribed positive gauge
level; this is the boundary exception in shell limit arguments. -/
theorem ae_gauge_ne {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {r : ℝ} (hr : 0 < r) : ∀ᵐ x : Fin N → ℝ, ν x ≠ r := by
  rw [ae_iff]
  simpa only [not_not] using volume_gauge_level G hν hr

/-- Splitting a closed shell introduces only a null common
boundary (BB proof of (6.39), p. 274). -/
theorem integral_gaugeShell_add {ν f : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    {r s R : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hsR : s ≤ R) :
    (∫ x in gaugeShell ν r R, f x) =
      (∫ x in gaugeShell ν r s, f x) + ∫ x in gaugeShell ν s R, f x := by
  have he : gaugeShell ν r R = gaugeShell ν r s ∪ gaugeShell ν s R := by
    ext x
    simp only [gaugeShell, mem_ofPred_eq, mem_union]
    constructor
    · intro hx
      by_cases h : ν x ≤ s
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨(not_le.mp h).le, hx.2⟩
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans hsR⟩
      · exact ⟨hrs.trans h.1, h.2⟩
  have hd : AEDisjoint volume (gaugeShell ν r s) (gaugeShell ν s R) := by
    change volume (gaugeShell ν r s ∩ gaugeShell ν s R) = 0
    apply measure_mono_null _ (volume_gauge_level G hν (hr.trans_le hrs))
    intro x hx
    exact le_antisymm hx.1.2 hx.2.1
  rw [he]
  exact setIntegral_union₀ hd (measurableSet_gaugeShell hν s R).nullMeasurableSet
    (integrableOn_gaugeShell hν hf hr) (integrableOn_gaugeShell hν hf (hr.trans_le hrs))

end RothschildStein.H1
