-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CoordinateReflection
public import RothschildStein.P1.DifferentialReflectionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1

/-- A reflected multi-index derivative `euclideanPartial` has its precise
ordinary-order sign, using only the corresponding punctured regularity. -/
theorem euclideanPartial_comp_neg {N : ℕ} (a : Fin N → ℕ)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    euclideanPartial a (fun y => f (-y)) x =
      (-1 : ℝ) ^ (∑ j, a j) * euclideanPartial a f (-x) := by
  have h := coordinateWord_comp_neg (G2.coordinateWord a)
    (by simpa only [G2.coordinateWord_length] using hf) x hx
  simpa only [G2.coordinate_word_partial, G2.coordinateWord_length] using h

/-- The concrete reflected differential operator satisfies
BB (11.12), p. 546, for every punctured kernel with the exact finite
regularity consumed by its effective indices. -/
theorem differentialReflection_apply {N : ℕ} (P : SmoothDifferentialOperator N)
    {f : (Fin N → ℝ) → ℝ}
    (hf : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    (differentialReflection P).apply f (-x) = P.apply (fun y => f (-y)) x := by
  unfold SmoothDifferentialOperator.apply
  rw [differentialReflection_indices]
  apply Finset.sum_congr rfl
  intro a ha
  rw [differentialReflection_coefficient, neg_neg, euclideanPartial_comp_neg a (hf a ha) hx]
  ring

/-- Reflection preserves the homogeneous differential degree
for every smooth-coefficient operator, not just invariant ones. -/
theorem differentialReflection_homogeneous {N : ℕ} (G : HomogeneousGroup N)
    (P : SmoothDifferentialOperator N) {β : ℝ} (hP : P.IsHomogeneous G β) :
    (differentialReflection P).IsHomogeneous G β := by
  apply (G2.operator_homogeneous_iff_scaled_coefficients G _ β).mpr
  intro a ha t ht x
  have hc := (G2.operator_homogeneous_iff_scaled_coefficients G P β).mp hP a ha t ht (-x)
  have hneg : G.dilate t (-x) = -G.dilate t x := by
    ext j
    simp [HomogeneousGroup.dilate, coordinateDilation]
  simp only [differentialReflection_coefficient]
  rw [hneg] at hc
  calc
    _ = (-1 : ℝ) ^ (∑ j, a j) *
        (P.coefficient a (-x) * t ^ (∑ j, G.weight j * a j)) := by ring
    _ = (-1 : ℝ) ^ (∑ j, a j) * (t ^ β * P.coefficient a (-G.dilate t x)) := by rw [hc]
    _ = _ := by ring

end RothschildStein.P1
