-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.AdditiveGroup
public import RothschildStein.G2.MollifierDefs
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- A symmetric compactly supported smooth bump in the coordinate ball of radius one half (BB Lemma 2.8, p. 72). -/
def euclideanBump (n : ℕ) : ContDiffBump (0 : Fin n → ℝ) :=
  ⟨1/4,1/2,by norm_num,by norm_num⟩

/-- The real normalized even mollifier (BB Lemma 2.8, p. 72). -/
def euclideanJ (n : ℕ) : (Fin n → ℝ) → ℝ := (euclideanBump n).normed volume

/-- The mollifier is smooth and has compact support
(BB Lemma 2.8, p. 72). -/
theorem euclideanJ_smooth_compact (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanJ n) ∧ HasCompactSupport (euclideanJ n) :=
  ⟨(euclideanBump n).contDiff_normed,(euclideanBump n).hasCompactSupport_normed⟩

/-- The mollifier is nonnegative and has mass one
(BB Lemma 2.8, p. 72). -/
theorem euclideanJ_normalized (n : ℕ) :
    (∀ x, 0 ≤ euclideanJ n x) ∧ (∫ x, euclideanJ n x) = 1 :=
  ⟨(euclideanBump n).nonneg_normed,(euclideanBump n).integral_normed⟩

/-- The normalized mollifier is even, as needed in the Friedrichs identity (BB p. 73). -/
theorem euclideanJ_even (n : ℕ) (x : Fin n → ℝ) : euclideanJ n (-x) = euclideanJ n x :=
  (euclideanBump n).normed_neg x

/-- The mollifier vanishes outside the half-unit ball
(BB Lemma 2.8, p. 72). -/
theorem euclideanJ_vanish (x : Fin n → ℝ) (hx : 1/2 ≤ ‖x‖) : euclideanJ n x = 0 := by
  unfold euclideanJ ContDiffBump.normed
  rw [(euclideanBump n).zero_of_le_dist (by simpa [euclideanBump,dist_zero_right] using hx)]
  simp

/-- The Euclidean mollifier has the normalization required in the Friedrichs construction (BB Lemma 2.8, p. 72; Proposition 3.48). -/
def euclideanGroupMollifier (hn : 0 < n) :
    RothschildStein.G2.GroupMollifier (additiveCoordinateGroup hn) (additiveCoordinateNorm hn) where
  toFun := euclideanJ n
  smooth := (euclideanJ_smooth_compact n).1
  compact := (euclideanJ_smooth_compact n).2
  nonneg := (euclideanJ_normalized n).1
  integral_eq_one := (euclideanJ_normalized n).2
  vanish := fun x hx => euclideanJ_vanish x (le_trans (by norm_num) hx)

end RothschildStein.S
