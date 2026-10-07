-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ACIntegralCurve

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace RothschildStein.G4

/-- Continuous a.e. forcing upgrades an AC curve to a classical
right integral curve, including the initial endpoint. -/
theorem ac_curve_hasDerivWithinAt {n : ℕ} {γ β : ℝ → (Fin n → ℝ)}
    (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hβ : ContinuousOn β (Icc 0 1))
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt γ (β t) t)
    {t : ℝ} (ht : t ∈ Ico 0 1) : HasDerivWithinAt γ (β t) (Ici t) t := by
  let clip : ℝ → ℝ := fun u => max 0 (min 1 u)
  have hc : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hclip : ∀ u, clip u ∈ Icc (0 : ℝ) 1 := by
    intro u
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclipEq : ∀ u ∈ Icc (0 : ℝ) 1, clip u = u := by
    intro u hu
    dsimp [clip]
    rw [min_eq_right hu.2, max_eq_right hu.1]
  let b : ℝ → (Fin n → ℝ) := β ∘ clip
  have hb : Continuous b := hβ.comp_continuous hc hclip
  have hbeq : ∀ u ∈ Icc (0 : ℝ) 1, b u = β u := by
    intro u hu
    change β (clip u) = β u
    rw [hclipEq u hu]
  have hdb : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt γ (b u) u := by
    filter_upwards [hd, ae_restrict_mem measurableSet_Icc] with u hu humem
    rw [hbeq u humem]
    exact hu
  apply hasDerivWithinAt_pi.mpr
  intro i
  let F : ℝ → ℝ := fun u => γ 0 i + ∫ v in (0 : ℝ)..u, b v i
  have hbi : Continuous (fun u => b u i) := (continuous_apply i).comp hb
  have hF : HasDerivAt F (b t i) t := by
    exact (intervalIntegral.integral_hasDerivAt_right (hbi.intervalIntegrable 0 t)
      hbi.aestronglyMeasurable.stronglyMeasurableAtFilter hbi.continuousAt).const_add _
  have he : ∀ u ∈ Icc (0 : ℝ) 1, γ u i = F u :=
    fun u hu => ac_curve_coordinate_integral hac hdb hu i
  have hnear : (fun u => γ u i) =ᶠ[𝓝[Ici t] t] F := by
    filter_upwards [Icc_mem_nhdsGE ht.2] with u hu
    exact he u ⟨ht.1.trans hu.1, hu.2⟩
  rw [← hbeq t ⟨ht.1, ht.2.le⟩]
  exact hF.hasDerivWithinAt.congr_of_eventuallyEq hnear (he t ⟨ht.1, ht.2.le⟩)

end RothschildStein.G4
