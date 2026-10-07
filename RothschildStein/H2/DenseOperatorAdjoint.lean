-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.H2
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Y : Type*}

/-- An adjoint identity on a dense range extends in both arguments. -/
theorem adjoint_of_denseRange {e : Y → H} (he : DenseRange e)
    (T T' : H →L[ℝ] H)
    (hadj : ∀ f g, inner ℝ (T (e f)) (e g) = inner ℝ (e f) (T' (e g))) :
    ∀ v w, inner ℝ (T v) w = inner ℝ v (T' w) := by
  have hf : ∀ f w, inner ℝ (T (e f)) w = inner ℝ (e f) (T' w) := by
    intro f w
    exact he.induction_on w (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner T'.continuous)) (hadj f)
  intro v w
  exact he.induction_on v (isClosed_eq (T.continuous.inner continuous_const)
    (continuous_id.inner continuous_const)) (fun f => hf f w)

/-- Continuous linear maps agreeing on a dense range are equal. -/
theorem operator_unique_of_denseRange {e : Y → H} (he : DenseRange e)
    (T S : H →L[ℝ] H) (hagree : ∀ f, T (e f) = S (e f)) : T = S := by
  apply ContinuousLinearMap.ext
  intro v
  exact he.induction_on v (isClosed_eq T.continuous S.continuous) hagree

end RothschildStein.H2
