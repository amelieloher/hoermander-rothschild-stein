-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ParabolicLocalizedData
public import HeatKernel.Bridge.RestrictedTensorIdentity
public import HeatKernel.Bridge.TensorFormTests
public import HeatKernel.Bridge.LocalizedEnergyPairings
public import HeatKernel.Form.ParabolicEnergyCurves
public import HeatKernel.Bridge.ParabolicCoefficientBounds
import Mathlib.Tactic.Linter

/-! # One weak gradient for all localized stationary energy tests -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- One original weak gradient satisfies the literal energy identity on all compact
interior cylinders, for all smooth temporal tests and stationary form tests. -/
theorem IsLocalWeakSolution.exists_uniform_energy_test_identity {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧
      ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    : ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i,
        hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t)) ∧
      HasLocalParabolicEnergyBounds I U u g ∧
      ∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
        IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
      ∀ (V : Opens (Fin N → ℝ)), (V : Set (Fin N → ℝ)) ⊆ K →
      ∀ (ψ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
      ∀ v : zeroBoundaryGraph V (G.horizontalFields hq),
        Integrable (fun z : ℝ × (Fin N → ℝ) =>
          (-(deriv ψ z.1) * u z.1 z.2) * (v : GradientSpace (N := N) ⊤ q).fst z.2)
          ((volume.restrict J).prod volume) ∧
        (∀ i, Integrable (fun z : ℝ × (Fin N → ℝ) =>
          (ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) *
            (v : GradientSpace (N := N) ⊤ q).snd i z.2) ((volume.restrict J).prod volume)) ∧
        (∫ z : ℝ × (Fin N → ℝ), (-(deriv ψ z.1) * u z.1 z.2) *
          (v : GradientSpace (N := N) ⊤ q).fst z.2 ∂(volume.restrict J).prod volume) +
          (∑ i, ∫ z : ℝ × (Fin N → ℝ),
            (ψ z.1 * ∑ j, a z.1 z.2 i j * g j z.1 z.2) *
              (v : GradientSpace (N := N) ⊤ q).snd i z.2 ∂(volume.restrict J).prod volume) = 0 := by
  have hu' := hu
  obtain ⟨_, _, _, hgb, _⟩ := hu'
  have hrestricted := hu.exists_restricted_tensor_identity G hq hqpos hw hspan a I U
  obtain ⟨g', hg', hgb', hweak'⟩ := hrestricted
  have hgbOriginal := hgb
  refine ⟨g', hg', ?_, ?_⟩
  · intro J K hJ hJI hK hKU
    exact ⟨(hgbOriginal J K hJ hJI hK hKU).1, hgb' J K hJ hJI hK hKU⟩
  · intro J K hJ hJI hK hKU V hVK ψ hψ hcψ hsψ v
    have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJ.measure_ne_top
    obtain ⟨T, F, hT, hF⟩ := hu.exists_localized_form_data G hq hqpos hw hspan a I U
      hJ hJI hK hKU g' (hgb' J K hJ hJI hK hKU)
      (fun i j => (ha i j).aestronglyMeasurable)
      (ae_norm_parabolic_coefficient_entry_le a hlower hbound (J ×ˢ K)) hψ hcψ
    have he : timeIntegratedFormTest (volume.restrict J) (G.horizontalFields hq) T F
        ⟨v, zeroBoundaryGraph_le_energyGraph V (G.horizontalFields hq) v.property⟩ = 0 := by
      apply timeIntegratedFormTest_eq_zero_of_tensor_identity (volume.restrict J) V
        (G.horizontalFields hq) hVK u g' a ψ T F hT hF _ v
      intro φ hφ hcφ hsφ
      exact (hweak' J hJI ψ hψ hcψ hsψ φ hφ hcφ (hsφ.trans (hVK.trans hKU))).2
    obtain ⟨hi, hj, hid⟩ := localized_form_test_pairings (volume.restrict J) V
      (G.horizontalFields hq) hVK (fun z => -(deriv ψ z.1) * u z.1 z.2)
      (fun i z => ψ z.1 * ∑ j, a z.1 z.2 i j * g' j z.1 z.2) T F hT hF v
    exact ⟨hi, hj, hid.symm.trans he⟩

end HeatKernel
