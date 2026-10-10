-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalSobolev
public import HeatKernel.Bridge.SquareIntegrableSlices
public import HeatKernel.Definitions.IsLocalWeakSolution
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff
import Mathlib.Tactic.Linter

/-! # Compatibility of parabolic weak gradients and horizontal form representatives -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Almost every local Sobolev slice has local energy representatives with the
specified weak gradient. The local Sobolev slice hypothesis is explicit. -/
theorem ae_exists_local_energy_representatives_of_slice_sobolev {N q : ℕ}
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hu : ∀ᵐ t ∂(volume.restrict (I : Set ℝ)), memSobolevXLoc noDriftWeight X U 1 2 (u t))
    (hg : ∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i, hasWeakWordDeriv X U [i] (u t) (g i t)) :
    ∀ᵐ t ∂(volume.restrict (I : Set ℝ)), MemLocalEnergy U X (u t) ∧
      ∀ V : Opens (Fin N → ℝ), IsCompact (closure (V : Set (Fin N → ℝ))) →
        closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) →
        ∃ w : energyGraph (N := N) ⊤ X,
          (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] u t ∧
          ∀ i, energyGradient ⊤ X w i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g i t := by
  filter_upwards [hu, hg] with t ht hgt
  have hlocal := (memLocalEnergy_iff_memSobolevXLoc U X hX).mpr ht
  refine ⟨hlocal, ?_⟩
  intro V hVc hVU
  obtain ⟨w, hw⟩ := hlocal.2 V hVc hVU
  exact ⟨w, hw, fun i => energyGradient_eq_of_local_weak_derivative U V
    (subset_closure.trans hVU) X hX w hw i (hgt i)⟩

end HeatKernel
