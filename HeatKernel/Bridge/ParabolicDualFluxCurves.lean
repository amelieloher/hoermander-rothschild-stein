-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalizedDualFluxCurves
public import HeatKernel.Form.ParabolicEnergyCurves
import Mathlib.Tactic.Linter

/-! # Local parabolic energy bounds yield zero-boundary dual flux curves -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Compact-cylinder gradient bounds and bounded measurable coefficients supply
an L² dual flux on every contained zero-boundary spatial domain. -/
theorem HasLocalParabolicEnergyBounds.exists_zeroBoundary_dual_flux_curve {N q : ℕ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (he : HasLocalParabolicEnergyBounds I U u g)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    {C : ℝ} (hb : ∀ i j, ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume, ‖a z.1 z.2 i j‖ ≤ C)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (V : Opens (Fin N → ℝ)) (hVK : (V : Set (Fin N → ℝ)) ⊆ K) :
    ∃ F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ), MemLp F 2 (volume.restrict J) ∧
      ∀ᵐ t ∂volume.restrict J, ∀ v : zeroBoundaryGraph V X,
        F t v = ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
          (v : GradientSpace (N := N) ⊤ q).snd i x := by
  have hgp (i : Fin q) : MemLp (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) 2
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using
      (he J K hJ hJI hK hKU).2 i
  have hap (i j : Fin q) : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using
      (ha i j).aestronglyMeasurable.restrict (s := J ×ˢ K)
  have hbp (i j : Fin q) : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂((volume.restrict J).prod (volume.restrict K)), ‖a z.1 z.2 i j‖ ≤ C := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using
      (ae_restrict_of_ae (s := J ×ˢ K) (hb i j))
  exact exists_localized_dual_matrix_flux_curve V X hK.measurableSet hVK
    (fun i j z => a z.1 z.2 i j) (fun j z => g j z.1 z.2) hap hgp hbp

end HeatKernel
