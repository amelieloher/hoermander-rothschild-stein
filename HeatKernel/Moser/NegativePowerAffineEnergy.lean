-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerEnergyEndpoints
public import HeatKernel.Moser.WeakSolutionAffineIntegrals

/-! Reciprocal-power energies after restoring the constant part of the scalar test. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The fixed-test correction cancels the linear term in the normalized primitive. -/
theorem negative_power_affine_energy_eq {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    W.affineEnergy (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
      w (c ^ (-p - 1)) z = ∫ x, W.toFun x *
        (-(((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) - c ^ (-p)) / p) := by
  rw [W.affineEnergy_eq_integral _ w _ hw z]
  apply integral_congr_ae
  filter_upwards [hz] with x hx
  rw [negative_power_test_primitive hc hp hx]
  congr 1
  ring

/-- Restoring the constant derivative correction gives the uncentered scalar power. -/
theorem negative_power_affine_test_value_ae {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    (W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
      w (c ^ (-p - 1)) z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p - 1) := by
  filter_upwards [W.affineEnergyMap_value_ae hX
    (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith)) w _ hw z, hz]
    with x hx hpos
  rw [hx]
  have he : (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith)).toFun
      ((z : GradientSpace (N := N) ⊤ q).fst x) =
      ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p - 1) - c ^ (-p - 1) :=
    Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := -p - 1) hpos
  rw [he, sub_add_cancel]

end HeatKernel
