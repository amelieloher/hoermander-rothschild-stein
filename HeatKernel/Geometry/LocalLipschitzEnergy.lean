-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.AnnularCutoff
public import HeatKernel.Geometry.CompactLipschitzEnergy

/-! Compact energy representatives of Lipschitz functions near compact sets. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
open scoped NNReal ENNReal BigOperators
namespace HeatKernel

/-- On an open set where a form vector represents a function, its energy gradient is
any given weak horizontal gradient of that function. -/
theorem energyGradient_eq_weak_derivative_locally {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    (V : Opens (Fin N → ℝ)) {f : (Fin N → ℝ) → ℝ}
    (hu : energyInclusion ⊤ X u =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f)
    (g : Fin q → (Fin N → ℝ) → ℝ) (hg : ∀ i, hasWeakWordDeriv X V [i] f (g i)) :
    ∀ i, energyGradient ⊤ X u i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g i := by
  have hw := energyGraph_le_weakGradientGraph ⊤ X (fun i => (hX i).contDiffOn) u.property
  intro i
  have hr := S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) (hw i)
  exact S.hasWeakWordDeriv_unique X V
    (S.hasWeakWordDeriv_congr_ae X V hr hu Filter.EventuallyEq.rfl) (hg i)

end HeatKernel
