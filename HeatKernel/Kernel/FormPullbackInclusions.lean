-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SpatialFormPullbacks

/-! # Compatibility of energy and spatial pullbacks

The energy actions and spatial L² actions use the same pullback maps.
The horizontal energy inclusion therefore intertwines both actions.
-/

@[expose] public section

noncomputable section

open RothschildStein

namespace HeatKernel

/-- The energy inclusion intertwines left translation with its spatial L² pullback. -/
theorem energyInclusion_energyLeftTranslation_eq_spatial {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyInclusion ⊤ (G.horizontalFields hq) (energyLeftTranslation G hq y u) =
      spatialLeftTranslation G y (energyInclusion ⊤ (G.horizontalFields hq) u) := rfl

/-- The energy inclusion intertwines normalized dilation with its spatial L² pullback. -/
theorem energyInclusion_normalizedEnergyDilation_eq_spatial {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyInclusion ⊤ (G.horizontalFields hq) (normalizedEnergyDilation G hq hw hr u) =
      spatialNormalizedDilation G hr (energyInclusion ⊤ (G.horizontalFields hq) u) := by
  simp only [normalizedEnergyDilation, smul_apply, map_smul]
  rfl

end HeatKernel
