-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ZeroPreservingShiftedScalars
public import HeatKernel.Moser.NonlinearEnergyDifferentiability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Scalar tests and primitive conventions for nonlinear weak-solution testing

Tests vanish at zero and have a Lipschitz scalar map, with at most countably many
exceptional differentiability levels. The primitive is normalized at zero. In particular,
centering a power test also subtracts a linear term from its primitive; this term is part
of the energy. Positive powers outside the Lipschitz range require truncation.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace HeatKernel

/-- A scalar test acting continuously on the horizontal energy graph. -/
structure WeakSolutionScalarTest where
  /-- The pointwise scalar test. -/
  toFun : ℝ → ℝ
  /-- A global Lipschitz constant. -/
  bound : ℝ≥0
  /-- The Lipschitz estimate. -/
  lipschitz : LipschitzWith bound toFun
  /-- Zero preservation ensures integrability on infinite-volume domains. -/
  map_zero : toFun 0 = 0
  /-- Exceptional levels for the piecewise differentiability condition. -/
  exceptional : Set ℝ
  /-- Only countably many exceptional levels are needed. -/
  countable_exceptional : exceptional.Countable
  /-- Smoothness away from the exceptional levels. -/
  contDiffAt : ∀ s ∉ exceptional, ContDiffAt ℝ 1 toFun s

/-- The scalar energy associated to a test, including its normalization terms. -/
def WeakSolutionScalarTest.primitive (T : WeakSolutionScalarTest) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, T.toFun t

/-- The normalized primitive vanishes at zero. -/
@[simp] theorem WeakSolutionScalarTest.primitive_zero (T : WeakSolutionScalarTest) :
    T.primitive 0 = 0 := by simp [WeakSolutionScalarTest.primitive]

/-- The primitive has precisely the chosen test as its derivative, including at kink levels. -/
theorem WeakSolutionScalarTest.hasDerivAt_primitive (T : WeakSolutionScalarTest) (s : ℝ) :
    HasDerivAt T.primitive (T.toFun s) s := by
  exact (T.lipschitz.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- Centered real powers of exponent at most one, including all negative powers. -/
def shiftedRpowWeakSolutionTest {c p : ℝ} (hc : 0 < c) (hp : p ≤ 1) : WeakSolutionScalarTest where
  toFun := Sobolev.zeroPreservingShiftedRpow c p
  bound := Real.toNNReal (|p| * c^(p-1))
  lipschitz := Sobolev.lipschitzWith_zeroPreservingShiftedRpow hc hp
  map_zero := Sobolev.zeroPreservingShiftedRpow_zero c p
  exceptional := {0}
  countable_exceptional := countable_singleton 0
  contDiffAt := fun s hs => Sobolev.contDiffAt_zeroPreservingShiftedRpow hc
    (by simpa only [mem_singleton_iff] using hs)

end HeatKernel
