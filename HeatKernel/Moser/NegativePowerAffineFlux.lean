-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerAffineEnergy
public import HeatKernel.Moser.NegativePowerShiftedGradient
public import HeatKernel.Moser.WeakSolutionSpatialTransport
import all Mathlib.Basic.Real.Basic

/-! Original coefficient flux of affine-corrected reciprocal-power tests. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- The affine correction restores the uncentered power in the weight-gradient
term without changing the principal negative-power derivative. -/
theorem WeakSolutionSpatialWeight.negative_power_affine_gradient_ae {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (z w : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (i : Fin q) :
    (W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
      w (c ^ (-p - 1)) z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => W.toFun x * (((-p - 1) *
        ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p - 2)) *
        (z : GradientSpace (N := N) ⊤ q).snd i x) +
        W.gradient i x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p - 1) := by
  simpa only [show -p - 1 - 1 = -p - 2 by ring] using
    W.shifted_rpow_affine_gradient_ae hX hc (r := -p - 1) (by linarith) z w hz hdw i

end HeatKernel
