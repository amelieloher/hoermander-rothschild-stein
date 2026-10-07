-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ReversedOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The operator is left invariant (BB p. 254). -/
theorem StandingHypotheses.operator_leftInvariant (H : StandingHypotheses G q) :
    G2.IsLeftInvariantOperator G (sumSquaresWithDrift H.fields) := by
  intro f hf y
  funext x
  have h0 := congrFun ((H.invariant 0).operator G f hf y) x
  have hi : ∀ i : Fin q, G2.IsLeftInvariantOperator G
      (fieldDerivative (H.fields i.succ) ∘ fieldDerivative (H.fields i.succ)) := by
    intro i
    exact ((H.invariant i.succ).operator G).comp G ((H.invariant i.succ).operator G)
      (fun g hg => smooth_fieldDerivative _ (H.fields_smooth G i.succ) g hg)
  unfold sumSquaresWithDrift
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (hi i f hf y) x

/-- The transpose is also left invariant (BB p. 254). -/
theorem StandingHypotheses.transpose_leftInvariant (H : StandingHypotheses G q) :
    G2.IsLeftInvariantOperator G (sumSquaresWithDriftTranspose H.fields) := by
  intro f hf y
  have h := (H.reverseDrift G).operator_leftInvariant G f hf y
  have he : ∀ g, ContDiff ℝ (⊤ : ℕ∞) g →
      sumSquaresWithDrift (H.reverseDrift G).fields g = sumSquaresWithDriftTranspose H.fields g := by
    intro g hg
    funext x
    exact H.reverseDrift_operator G g hg x
  rw [he _ (hf.comp (G2.contDiff_leftTranslation G y)), he f hf] at h
  exact h

end RothschildStein.H1
