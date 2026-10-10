-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicMeasurability
public import HeatKernel.Form.ParabolicEnergyCurves
import Mathlib.Tactic

/-! # Local parabolic energy bounds under group scaling -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein RothschildStein.G2
open scoped ENNReal
namespace HeatKernel

/-- Compact-cylinder energy bounds transport under parabolic coordinates, with the
same local domains as the transported weak equation and the literal gradient factor r. -/
theorem HasLocalParabolicEnergyBounds.parabolic_pullback {N q : ℕ}
    (G : HomogeneousGroup N) (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : HasLocalParabolicEnergyBounds I U u g)
    (J : Opens ℝ) (V : Opens (Fin N → ℝ))
    (htdom : ∀ t ∈ (J : Set ℝ), t₀ + r ^ 2 * t ∈ (I : Set ℝ))
    (hsdom : ∀ x ∈ (V : Set (Fin N → ℝ)), G.mul x₀ (G.dilate r x) ∈ (U : Set _)) :
    let T := parabolicGroupHomeomorph G t₀ x₀ r hr
    HasLocalParabolicEnergyBounds J V
      (fun t x => u (T (t, x)).1 (T (t, x)).2)
      (fun i t x => r * g i (T (t, x)).1 (T (t, x)).2) := by
  intro T j k hj hjJ hk hkV
  let A := parabolicTimeHomeomorph t₀ r hr
  let B := (dilationHomeomorph G r hr).trans (leftTranslationHomeomorph G x₀)
  let j₀ := A '' j
  let k₀ := B '' k
  have hj₀ : IsCompact j₀ := hj.image A.continuous
  have hk₀ : IsCompact k₀ := hk.image B.continuous
  have hj₀I : j₀ ⊆ (I : Set ℝ) := by
    rintro _ ⟨t, ht, rfl⟩
    exact htdom t (hjJ ht)
  have hk₀U : k₀ ⊆ (U : Set (Fin N → ℝ)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsdom x (hkV hx)
  obtain ⟨hS, hg⟩ := h j₀ k₀ hj₀ hj₀I hk₀ hk₀U
  have hmA : Measure.map A volume = ENNReal.ofReal ((r ^ 2)⁻¹) • volume :=
    map_parabolicTimeHomeomorph_volume t₀ r hr
  have hmB : Measure.map B volume =
      ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹) • volume :=
    map_leftTranslation_dilation_volume G x₀ r hr
  have hpreA : A ⁻¹' j₀ = j := A.injective.preimage_image j
  have hpreB : B ⁻¹' k₀ = k := B.injective.preimage_image k
  let S := essSup (fun t => eLpNorm (u t) 2 (volume.restrict k₀)) (volume.restrict j₀)
  let C := ENNReal.ofReal ((r ^ G.homogeneousDimension)⁻¹) ^ (1 / 2 : ℝ)
  have ht : ∀ᵐ t ∂volume.restrict j, eLpNorm (u (A t)) 2 (volume.restrict k₀) ≤ S := by
    have ht' := (ae_restrict_comp_iff_of_scaled_measure A volume hmA
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hr))).ne' j₀
      (fun t => eLpNorm (u t) 2 (volume.restrict k₀) ≤ S)).mpr
        (ENNReal.ae_le_essSup _)
    rwa [hpreA] at ht'
  have hnorm : ∀ t, eLpNorm ((u (A t)) ∘ B) 2 (volume.restrict k) =
      C * eLpNorm (u (A t)) 2 (volume.restrict k₀) := by
    intro t
    have hn := eLpNorm_two_comp_restrict_of_scaled_measure B volume hmB (u (A t)) k₀
    rwa [hpreB] at hn
  constructor
  · change essSup (fun t => eLpNorm ((u (A t)) ∘ B) 2 (volume.restrict k))
      (volume.restrict j) < ⊤
    have hbound : essSup (fun t => eLpNorm ((u (A t)) ∘ B) 2 (volume.restrict k))
        (volume.restrict j) ≤ C * S := by
      refine essSup_le_of_ae_le (C * S) ?_ (by isBoundedDefault)
      filter_upwards [ht] with t ht
      rw [hnorm t]
      exact mul_le_mul' le_rfl ht
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))
        ENNReal.ofReal_ne_top) hS)
  · intro i
    have hsub : j ×ˢ k ⊆ T ⁻¹' (j₀ ×ˢ k₀) := by
      intro z hz
      exact ⟨⟨z.1, hz.1, rfl⟩, ⟨z.2, hz.2, rfl⟩⟩
    exact (memLp_parabolic_pullback G t₀ x₀ r hr (hg i) hsub).const_mul r

end HeatKernel
