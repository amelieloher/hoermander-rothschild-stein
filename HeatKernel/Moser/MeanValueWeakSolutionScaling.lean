-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueWeakGradientScaling
public import HeatKernel.Moser.MeanValueLocalEnergyScaling
public import HeatKernel.Moser.MeanValueWeakEquationScaling
public import HeatKernel.Definitions.IsLocalWeakSolution
import Mathlib.Tactic

/-! # Parabolic group scaling of local weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A local weak solution pulls back under parabolic group coordinates. Its actual
weak gradient is multiplied by r; measurability, local energy bounds and the weak
spacetime equation are all transported on the indicated cylinder. -/
theorem IsLocalWeakSolution.parabolic_pullback {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ)) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (J : Opens ℝ) (V : Opens (Fin N → ℝ))
    (htdom : ∀ t ∈ (J : Set ℝ), t₀ + r ^ 2 * t ∈ (I : Set ℝ))
    (hsdom : ∀ x ∈ (V : Set (Fin N → ℝ)), G.mul x₀ (G.dilate r x) ∈ (U : Set _)) :
    let T := parabolicGroupHomeomorph G t₀ x₀ r hr
    IsLocalWeakSolution G hq hqpos hw hspan
      (fun t x i j => a (T (t, x)).1 (T (t, x)).2 i j) J V
      (fun t x => u (T (t, x)).1 (T (t, x)).2) := by
  intro T
  rcases hu with ⟨huM, g, hg, hb, ht⟩
  have hdom : (J : Set ℝ) ×ˢ (V : Set (Fin N → ℝ)) ⊆
      T ⁻¹' ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))) := by
    intro z hz
    exact ⟨htdom z.1 hz.1, hsdom z.2 hz.2⟩
  refine ⟨aestronglyMeasurable_parabolic_pullback G t₀ x₀ r hr huM hdom,
    (fun i t x => r * g i (T (t, x)).1 (T (t, x)).2), ?_, ?_, ?_⟩
  · let A := parabolicTimeHomeomorph t₀ r hr
    have hmA : Measure.map A volume = ENNReal.ofReal ((r ^ 2)⁻¹) • volume :=
      map_parabolicTimeHomeomorph_volume t₀ r hr
    have hA : (J : Set ℝ) ⊆ A ⁻¹' (I : Set ℝ) := htdom
    have hg' := (ae_restrict_comp_iff_of_scaled_measure A volume hmA
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hr))).ne' (I : Set ℝ)
      (fun t => ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t))).mpr hg
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hA hg'] with t hgt
    intro i
    exact hasWeakWordDeriv_spatial_pullback G hq hw x₀ r hr U V hsdom i (hgt i)
  · exact HasLocalParabolicEnergyBounds.parabolic_pullback G t₀ x₀ r hr hb J V htdom hsdom
  · exact SatisfiesParabolicTestIdentity.parabolic_pullback G hq hw t₀ x₀ r hr ht J V hdom

end HeatKernel
