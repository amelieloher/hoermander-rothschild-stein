-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ACClassicalCurve
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal

namespace RothschildStein.G4

/-- Uniqueness between an actual AC control solution and a
classical flow on a common Lipschitz buffer. The initial time is the
closed interval endpoint, so no extension of the AC curve is assumed. -/
theorem ac_integralCurve_eqOn {n : ℕ} {S : Set (Fin n → ℝ)}
    {Z : (Fin n → ℝ) → (Fin n → ℝ)} {K : ℝ≥0}
    (hLip : LipschitzOnWith K Z S) (hZ : ContinuousOn Z S)
    {γ ψ : ℝ → (Fin n → ℝ)}
    (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hγS : MapsTo γ (Icc 0 1) S)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt γ (Z (γ t)) t)
    (hψ : ContinuousOn ψ (Icc 0 1)) (hψS : MapsTo ψ (Icc 0 1) S)
    (hψd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivAt ψ (Z (ψ t)) t)
    (hinit : γ 0 = ψ 0) : EqOn γ ψ (Icc 0 1) := by
  have hγ : ContinuousOn γ (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using hac.continuousOn
  have hforcing : ContinuousOn (fun t => Z (γ t)) (Icc 0 1) := hZ.comp hγ hγS
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => Z) (s := fun _ => S)
    (fun _ _ => hLip) hγ (fun t ht => ac_curve_hasDerivWithinAt hac hforcing hd ht)
    (fun t ht => hγS ⟨ht.1, ht.2.le⟩) hψ
    (fun t ht => (hψd t ht).hasDerivWithinAt)
    (fun t ht => hψS ⟨ht.1, ht.2.le⟩) hinit

end RothschildStein.G4
