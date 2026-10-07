-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.WeightEstimates
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Hormander.B

/-- The Japanese-bracket power expressed directly through its squared bracket. -/
def radialWeight {E : Type*} [NormedAddCommGroup E] (x : E) (σ : ℝ) : ℝ :=
  bracketSq x ^ (σ / 2)

/-- The squared bracket is smooth as a real function on the Euclidean carrier. -/
theorem contDiff_bracketSq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ContDiff ℝ (⊤ : ℕ∞) (bracketSq : E → ℝ) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : E => 1 + ‖x‖ ^ 2)
  exact contDiff_const.add (contDiff_norm_sq (𝕜 := ℝ))

/-- Every radial weight is smooth, since its squared bracket is everywhere positive. -/
theorem contDiff_radialWeight {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialWeight (E := E) · σ) := by
  apply (contDiff_bracketSq (E := E)).rpow_const_of_ne
  intro x
  exact ne_of_gt (by unfold bracketSq; positivity)

end Hormander.B
