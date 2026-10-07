-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellDefs
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ}

/-- A punctured continuous kernel times a compact
continuous test is integrable on any closed set away from the origin. -/
theorem integrableOn_punctured_mul_compact
    {F g : (Fin N → ℝ) → ℝ} (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hg : Continuous g) (hs : HasCompactSupport g)
    {S : Set (Fin N → ℝ)} (hS : IsClosed S) (h0 : (0 : Fin N → ℝ) ∉ S) :
    IntegrableOn (fun w => F w * g w) S volume := by
  let K := tsupport g ∩ S
  have hK : IsCompact K := hs.inter_right hS
  have hFc : ContinuousOn F K := hF.mono (by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    exact h0 (he ▸ hx.2))
  have hi : IntegrableOn (fun w => F w * g w) K volume :=
    (hFc.mul hg.continuousOn).integrableOn_compact hK
  have hmeas : MeasurableSet K := hK.measurableSet
  rw [← integrable_indicator_iff hmeas] at hi
  rw [← integrable_indicator_iff hS.measurableSet]
  convert hi using 1
  funext w
  by_cases hw : w ∈ S
  · by_cases hg' : w ∈ tsupport g
    · rw [indicator_of_mem hw, indicator_of_mem (show w ∈ K from ⟨hg', hw⟩)]
    · rw [indicator_of_mem hw, indicator_of_notMem (show w ∉ K from fun h => hg' h.1),
        image_eq_zero_of_notMem_tsupport hg', mul_zero]
  · rw [indicator_of_notMem hw, indicator_of_notMem (show w ∉ K from fun h => hw h.2)]

end RothschildStein.H1
