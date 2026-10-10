-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalDualEnergyIdentity
public import HeatKernel.Bridge.SmoothCutoffDualLocalization
import Mathlib.Tactic.Linter

/-! # Smooth spatial localization of local dual energy identities -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The local dual energy identity supplies global form-dual curves after every
smooth compact spatial cutoff, including the cutoff derivative in the flux. -/
theorem HasLocalDualEnergyCurves.exists_smooth_localization {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : HasLocalDualEnergyCurves X a I U u g)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (V : Opens (Fin N → ℝ)) (hVK : (V : Set (Fin N → ℝ)) ⊆ K)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (V : Set (Fin N → ℝ))) :
    ∃ D F : ℝ → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ),
      IsDualEnergyPair (E := energyGraph (N := N) ⊤ X) J
        (fun t v => ∫ x, u t x * (φ x * (v : GradientSpace (N := N) ⊤ q).fst x))
        (fun t v => ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
          (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
            fieldDerivative (X i) φ x * (v : GradientSpace (N := N) ⊤ q).fst x)) D F := by
  obtain ⟨D, F, hpair⟩ := h J K hJ hJI hK hKU V hVK
  exact hpair.exists_smooth_cutoff_localization V X hX hφ hc hs

/-- Every interior smooth compact cutoff has a global dual energy pair;
the compact spatial neighborhood is chosen from its support. -/
theorem HasLocalDualEnergyCurves.exists_interior_cutoff_pair {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : HasLocalDualEnergyCurves X a I U u g)
    {J : Set ℝ}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (U : Set (Fin N → ℝ))) :
    ∃ D F : ℝ → (energyGraph (N := N) ⊤ X →L[ℝ] ℝ),
      IsDualEnergyPair (E := energyGraph (N := N) ⊤ X) J
        (fun t v => ∫ x, u t x * (φ x * (v : GradientSpace (N := N) ⊤ q).fst x))
        (fun t v => ∑ i, ∫ x, (∑ j, a t x i j * g j t x) *
          (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
            fieldDerivative (X i) φ x * (v : GradientSpace (N := N) ⊤ q).fst x)) D F := by
  obtain ⟨V, hφV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hc hs
  exact h.exists_smooth_localization hX hJ hJI hVc hVU V subset_closure hφ hc hφV

end HeatKernel
