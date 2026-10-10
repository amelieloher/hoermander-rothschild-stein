-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.NormalizedEnergyDilations
public import HeatKernel.Form.HorizontalActionEquivalences
import Mathlib.Tactic.Linter

/-! # Invertible normalized dilations and their spatial inner products -/

@[expose] public section

noncomputable section

open RothschildStein

namespace HeatKernel

/-- The normalized positive dilation is a continuous linear equivalence on the energy domain. -/
def normalizedEnergyDilationEquiv {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r) :
    energyGraph (N := N) ⊤ (G.horizontalFields hq) ≃L[ℝ]
      energyGraph (N := N) ⊤ (G.horizontalFields hq) where
  toFun := normalizedEnergyDilation G hq hw hr
  invFun u := (Real.sqrt (r ^ G.homogeneousDimension))⁻¹ •
    energyDilation G hq hw (inv_pos.mpr hr) u
  left_inv u := by
    have ha : Real.sqrt (r ^ G.homogeneousDimension) ≠ 0 :=
      (Real.sqrt_pos.mpr (pow_pos hr _)).ne'
    change (Real.sqrt (r ^ G.homogeneousDimension))⁻¹ •
      energyDilation G hq hw (inv_pos.mpr hr)
        (Real.sqrt (r ^ G.homogeneousDimension) • energyDilation G hq hw hr u) = u
    rw [map_smul, smul_smul, inv_mul_cancel₀ ha, one_smul, energyDilation_inv]
  right_inv u := by
    have ha : Real.sqrt (r ^ G.homogeneousDimension) ≠ 0 :=
      (Real.sqrt_pos.mpr (pow_pos hr _)).ne'
    change Real.sqrt (r ^ G.homogeneousDimension) •
      energyDilation G hq hw hr ((Real.sqrt (r ^ G.homogeneousDimension))⁻¹ •
        energyDilation G hq hw (inv_pos.mpr hr) u) = u
    rw [map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul, energyDilation_comp]
    simpa only [inv_mul_cancel₀ hr.ne'] using energyDilation_one G hq hw u
  map_add' := map_add (normalizedEnergyDilation G hq hw hr)
  map_smul' := map_smul (normalizedEnergyDilation G hq hw hr)
  continuous_toFun := (normalizedEnergyDilation G hq hw hr).continuous
  continuous_invFun := by
    simpa only [Pi.smul_def] using
      (energyDilation G hq hw (inv_pos.mpr hr)).continuous.const_smul
        ((Real.sqrt (r ^ G.homogeneousDimension))⁻¹)

end HeatKernel
