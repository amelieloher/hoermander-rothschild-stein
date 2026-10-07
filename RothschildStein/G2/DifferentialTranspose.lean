-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorInvariance
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory
open scoped BigOperators
variable {N : ℕ}

private theorem smooth_coordinate_word (l : List (Fin N))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (l.foldr
      (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) f) := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- Finite coordinate derivatives preserve smoothness. -/
theorem euclideanPartial_contDiff (a : Fin N → ℕ)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanPartial a f) := smooth_coordinate_word _ f hf

/-- The finite-coordinate formula for the formal transpose
(BB Definition 3.22 / transpose preceding Proposition 3.24, pp. 106–108). -/
def differentialTranspose (P : SmoothDifferentialOperator N)
    (g : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ a ∈ P.indices, (-1 : ℝ) ^ (∑ j, a j) *
    euclideanPartial a (fun y => P.coefficient a y * g y) x

/-- The formal transpose preserves smoothness (BB pp. 106–108). -/
theorem differentialTranspose_preservesSmooth (P : SmoothDifferentialOperator N) :
    PreservesSmooth (differentialTranspose P) := by
  intro g hg
  exact ContDiff.sum fun a ha => contDiff_const.mul
    (euclideanPartial_contDiff a _ ((P.smooth_coefficient a ha).mul hg))

/-- The transpose identity, allowing either factor to have compact support
(BB Proposition 3.24, p. 108). -/
def TransposeRelation
    (P Q : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → ∀ g, ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport f ∨ HasCompactSupport g →
    ∫ x, P f x * g x = ∫ x, f x * Q g x

/-- Smooth testing determines continuous functions pointwise. -/
theorem continuous_eq_of_test_pairings {f g : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ φ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, φ x * f x = ∫ x, φ x * g x) : f = g := by
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume) _ hf hg
  exact ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
    (by simpa only [smul_eq_mul] using h)

end RothschildStein.G2
