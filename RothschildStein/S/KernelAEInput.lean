-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsKernelDefs
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter
namespace RothschildStein.S
variable {n : ℕ}

/-- At nonzero scales a kernel operator depends only on
the input's Lebesgue almost-everywhere class. Affine invertibility
preserves null sets in the displacement variable (BB pp. 74–78;
representative). -/
theorem friedrichsKernelOp_eq_of_ae
    (K : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    {h g : (Fin n → ℝ) → ℝ} (hh : h =ᵐ[volume] g)
    {ε : ℝ} (hε : ε ≠ 0) :
    friedrichsKernelOp K h ε = friedrichsKernelOp K g ε := by
  funext x
  unfold friedrichsKernelOp
  apply integral_congr_ae
  have ht := (measurePreserving_add_left volume x).quasiMeasurePreserving.ae_eq_comp hh
  have hs := (Measure.quasiMeasurePreserving_smul (μ := volume) hε).ae_eq_comp ht
  filter_upwards [hs] with y hy
  change h (x+ε • y) = g (x+ε • y) at hy
  rw [hy]

end RothschildStein.S
