-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.CoordinateIntegration
public import RothschildStein.G2.TransposeHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Set MeasureTheory
open scoped BigOperators
variable {N : ℕ}

/-- The multi-index word has total multi-index length. -/
theorem coordinateWord_length (a : Fin N → ℕ) : (coordinateWord a).length = ∑ j, a j := by
  simp only [coordinateWord, List.length_flatMap, List.length_replicate,
    ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

/-- Coordinate derivatives preserve compact support. -/
theorem euclideanPartial_compact (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (euclideanPartial a f) := by
  rw [← coordinate_word_partial a f]
  exact coordinate_word_compact _ f hf

/-- The multi-index integration-by-parts formula with either factor compact
(BB transpose formula, pp. 106–108). -/
theorem integral_partial_mul (a : Fin N → ℕ) (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) :
    (∫ x, euclideanPartial a f x * g x) =
      (-1 : ℝ) ^ (∑ j, a j) * ∫ x, f x * euclideanPartial a g x := by
  have h := integral_coordinate_word (coordinateWord a) f g hf hg hc
  rw [coordinate_word_partial, coordinate_word_reverse_partial a g hg, coordinateWord_length] at h
  exact h

private theorem integrable_mul_compact (f g : (Fin N → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) : Integrable (fun x => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport
    (hc.elim (fun h => h.mul_right) (fun h => h.mul_left))

/-- The finite smooth-coefficient transpose satisfies its exact bilinear identity
(BB Proposition 3.24, p. 108; coordinate integration). -/
theorem differentialTranspose_relation (P : SmoothDifferentialOperator N) :
    TransposeRelation P.apply (differentialTranspose P) := by
  intro f hf g hg hc
  have hLi : ∀ a ∈ P.indices,
      Integrable (fun x => (P.coefficient a x * euclideanPartial a f x) * g x) := by
    intro a ha
    apply integrable_mul_compact _ _
      ((P.smooth_coefficient a ha).mul (euclideanPartial_contDiff a f hf)).continuous hg.continuous
    exact hc.imp (fun h => (euclideanPartial_compact a f h).mul_left) id
  have hRi : ∀ a ∈ P.indices,
      Integrable (fun x => f x * ((-1 : ℝ) ^ (∑ j, a j) *
        euclideanPartial a (fun y => P.coefficient a y * g y) x)) := by
    intro a ha
    apply integrable_mul_compact _ _ hf.continuous
      (continuous_const.mul (euclideanPartial_contDiff a _ ((P.smooth_coefficient a ha).mul hg)).continuous)
    exact hc.imp id (fun h => (euclideanPartial_compact a _ h.mul_left).mul_left)
  simp only [SmoothDifferentialOperator.apply, differentialTranspose, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ hLi, integral_finsetSum _ hRi]
  apply Finset.sum_congr rfl
  intro a ha
  have hcg : HasCompactSupport f ∨ HasCompactSupport (fun x => P.coefficient a x * g x) :=
    hc.imp id (fun h => h.mul_left)
  have h := integral_partial_mul a f (fun x => P.coefficient a x * g x) hf
    ((P.smooth_coefficient a ha).mul hg) hcg
  rw [show (fun x => (P.coefficient a x * euclideanPartial a f x) * g x) =
      (fun x => euclideanPartial a f x * (P.coefficient a x * g x)) by funext x; ring]
  rw [h]
  rw [show (fun x => f x * ((-1 : ℝ) ^ (∑ j, a j) *
      euclideanPartial a (fun y => P.coefficient a y * g y) x)) =
    (fun x => (-1 : ℝ) ^ (∑ j, a j) *
      (f x * euclideanPartial a (fun y => P.coefficient a y * g y) x)) by funext x; ring,
    integral_const_mul]

/-- The finite differential-operator transpose preserves homogeneity degree (BB p. 108). -/
theorem differentialTranspose_homogeneous (G : HomogeneousGroup N)
    (P : SmoothDifferentialOperator N) (β : ℝ) (hP : P.IsHomogeneous G β) :
    IsHomogeneousOperator G (differentialTranspose P) β :=
  transpose_homogeneous_of_relation G (differentialTranspose_relation P)
    (differentialTranspose_preservesSmooth P) hP

end RothschildStein.G2
