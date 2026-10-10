-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyScaling
public import HeatKernel.Form.ScaledEnergyOperators
public import HeatKernel.Form.HorizontalActionEquivalences
import Mathlib.Tactic.Linter

/-! # L²-normalized dilations on the horizontal energy domain -/

@[expose] public section

noncomputable section

open RothschildStein RothschildStein.G2

namespace HeatKernel

/-- Dilation normalized by the square root of its homogeneous Jacobian. -/
def normalizedEnergyDilation {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r) :
    energyGraph (N := N) ⊤ (G.horizontalFields hq) →L[ℝ]
      energyGraph (N := N) ⊤ (G.horizontalFields hq) :=
  Real.sqrt (r ^ G.homogeneousDimension) • energyDilation G hq hw hr

/-- The homogeneous Jacobian cancels the unnormalized energy scaling to leave degree two. -/
theorem homogeneousJacobian_mul_energyScale {N : ℕ} (G : HomogeneousGroup N)
    {r : ℝ} (hr : 0 < r) :
    r ^ G.homogeneousDimension * r ^ (2 - (G.homogeneousDimension : ℝ)) = r ^ (2 : ℕ) := by
  rw [Real.rpow_sub hr]
  simp only [Real.rpow_two, Real.rpow_natCast]
  field_simp [pow_ne_zero _ hr.ne']

/-- The normalized dilation scales the bilinear horizontal energy by the square of its factor. -/
theorem horizontalEnergy_normalizedEnergyDilation {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r : ℝ} (hr : 0 < r) (u v : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    horizontalEnergy ⊤ (G.horizontalFields hq) (normalizedEnergyDilation G hq hw hr u)
      (normalizedEnergyDilation G hq hw hr v) = r ^ 2 * horizontalEnergy ⊤ (G.horizontalFields hq) u v := by
  simp only [normalizedEnergyDilation, smul_apply, horizontalEnergy_smul_smul,
    ← pow_two, Real.sq_sqrt (pow_nonneg hr.le _), horizontalEnergy_energyDilation]
  rw [← _root_.mul_assoc, homogeneousJacobian_mul_energyScale G hr]

end HeatKernel
