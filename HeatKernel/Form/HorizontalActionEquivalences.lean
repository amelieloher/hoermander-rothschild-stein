-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.HorizontalActionIdentities
public import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Linter

/-! # Continuous linear equivalences induced by horizontal translations and dilations -/

@[expose] public section

noncomputable section

open RothschildStein RothschildStein.G2

namespace HeatKernel

/-- Left translation is a continuous linear equivalence of the horizontal energy Hilbert space. -/
def energyLeftTranslationEquiv {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ) :
    energyGraph (N := N) ⊤ (G.horizontalFields hq) ≃L[ℝ]
      energyGraph (N := N) ⊤ (G.horizontalFields hq) where
  toFun := energyLeftTranslation G hq y
  invFun := energyLeftTranslation G hq (G.inv y)
  left_inv := energyLeftTranslation_inv G hq y
  right_inv u := by rw [energyLeftTranslation_comp, inv_mul G, energyLeftTranslation_zero]
  map_add' := map_add (energyLeftTranslation G hq y)
  map_smul' := map_smul (energyLeftTranslation G hq y)
  continuous_toFun := (energyLeftTranslation G hq y).continuous
  continuous_invFun := (energyLeftTranslation G hq (G.inv y)).continuous

end HeatKernel
