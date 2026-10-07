-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Transpose
public import Hormander.Interface.HormanderAdjointTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The standing fields are smooth on every open set. -/
theorem StandingHypotheses.fields_contDiffOn (H : StandingHypotheses G q)
    (U : Set (Fin N → ℝ)) : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (H.fields i) U :=
  fun i => (H.fields_smooth G i).contDiffOn

/-- The adjoint test is the group-operator transpose (BB p. 254). -/
theorem StandingHypotheses.hormanderAdjointTest_eq_transpose (H : StandingHypotheses G q)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin N → ℝ) :
    Hormander.Interface.hormanderAdjointTest H.fields 0 φ x =
      sumSquaresWithDriftTranspose H.fields φ x := by
  have hdiv : ∀ i f, ContDiff ℝ (⊤ : ℕ∞) f → ∀ y,
      Hormander.Interface.euclideanDivergence (fun z => f z • H.fields i z) y =
        fieldDerivative (H.fields i) f y := by
    intro i f hf y
    have ht := congrFun (H.fieldTranspose_eq_neg G i f hf) y
    change -(Hormander.Interface.euclideanDivergence (fun z => f z • H.fields i z) y) =
      -fieldDerivative (H.fields i) f y at ht
    exact neg_injective ht
  unfold Hormander.Interface.hormanderAdjointTest
  rw [hdiv 0 φ hφ x, H.sumSquaresTranspose_formula G φ hφ x]
  simp only [Pi.zero_apply, zero_mul, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [hdiv i.succ φ hφ]
  exact hdiv i.succ (fieldDerivative (H.fields i.succ) φ)
    (smooth_fieldDerivative _ (H.fields_smooth G i.succ) φ hφ) x

end RothschildStein.H1
