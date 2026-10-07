-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

noncomputable section

open MeasureTheory WithLp
open scoped InnerProductSpace RealInnerProductSpace

namespace Hormander.F

/-- The coordinate map from the sup-norm Pi carrier `Fin N → ℝ` of the main statement to
the Hilbert carrier used by the distribution and Sobolev APIs. -/
def coordinateEquiv (N : ℕ) : (Fin N → ℝ) ≃L[ℝ] E₂ N :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm

@[simp] theorem coordinateEquiv_apply {N : ℕ} (x : Fin N → ℝ) :
    coordinateEquiv N x = toLp 2 x := rfl

@[simp] theorem coordinateEquiv_apply_symm_apply {N : ℕ} (x : E₂ N) :
    coordinateEquiv N ((coordinateEquiv N).symm x) = x := by
  exact (coordinateEquiv N).apply_symm_apply x

@[simp] theorem coordinateEquiv_symm_apply {N : ℕ} (x : E₂ N) :
    (coordinateEquiv N).symm x = WithLp.ofLp x := rfl

theorem coordinateEquiv_measurePreserving (N : ℕ) :
    MeasurePreserving (coordinateEquiv N) := by
  simpa only [coordinateEquiv, PiLp.coe_symm_continuousLinearEquiv] using
    (PiLp.volume_preserving_toLp (ι := Fin N))

theorem coordinateEquiv_symm_measurePreserving (N : ℕ) :
    MeasurePreserving (coordinateEquiv N).symm := by
  simpa only [coordinateEquiv, ContinuousLinearEquiv.symm_symm,
    PiLp.coe_continuousLinearEquiv] using
    (PiLp.volume_preserving_ofLp (ι := Fin N))

end Hormander.F
