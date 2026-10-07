-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FiniteCoordinateHomogeneity
public import RothschildStein.H1.HomogeneousDerivativeCancellation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- finite differentiability suffices for the exact
operator degree; only effective multi-indices consume derivatives. -/
theorem differentialOperator_punctured_homogeneity_finite
    (P : SmoothDifferentialOperator N) {k β : ℝ} (hP : P.IsHomogeneous G k)
    {f : (Fin N → ℝ) → ℝ}
    (hreg : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    {t : ℝ} (ht : 0 < t) {x : Fin N → ℝ} (hx : x ≠ 0) :
    P.apply f (G.dilate t x) = t ^ (β - k) * P.apply f x := by
  classical
  have hcoef := (G2.operator_homogeneous_iff_coefficients G P k).mp hP
  unfold SmoothDifferentialOperator.apply
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [hcoef a ha t ht x, euclideanPartial_punctured_homogeneity_finite G a (hreg a ha) hf ht hx]
  have he : ((∑ j, G.weight j * a j : ℕ) : ℝ) - k +
      (β - (∑ j, G.weight j * a j : ℕ)) = β - k := by ring
  have hp : t ^ (((∑ j, G.weight j * a j : ℕ) : ℝ) - k) *
      t ^ (β - (∑ j, G.weight j * a j : ℕ)) = t ^ (β - k) := by
    rw [← Real.rpow_add ht, he]
  calc
    _ = (t ^ (((∑ j, G.weight j * a j : ℕ) : ℝ) - k) *
      t ^ (β - (∑ j, G.weight j * a j : ℕ))) *
      (P.coefficient a x * euclideanPartial a f x) := by ring
    _ = _ := by rw [hp]

end RothschildStein.H1
