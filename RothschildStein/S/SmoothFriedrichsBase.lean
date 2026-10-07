-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothFriedrichsKernels
public import RothschildStein.S.FriedrichsBaseKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {n : ℕ}

/-- The base mollifier is a joint smooth kernel, including at
ε=0 (BB (2.8), pp. 75–76; preferred parameter encoding). -/
def smoothBaseFriedrichsKernel (n : ℕ) : SmoothFriedrichsKernel n where
  toFun := fun p => euclideanJ n p.1.2
  smooth := (euclideanJ_smooth_compact n).1.comp contDiff_fst.snd
  vanish := fun p hp => euclideanJ_vanish p.1.2 (le_trans (by norm_num) hp.le)

/-- The joint base family has mass one for all x and ε
(BB (2.8), p. 75). -/
theorem smoothBaseFriedrichsKernel_mean (ε : ℝ) (x : Fin n → ℝ) :
    (∫ y, (smoothBaseFriedrichsKernel n).family ε x y) = 1 :=
  (euclideanJ_normalized n).2

end RothschildStein.S
