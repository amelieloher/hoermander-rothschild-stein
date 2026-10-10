-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueWeakRestriction
public import HeatKernel.Moser.MeanValueInteriorCylinders
public import HeatKernel.Moser.MeanValueLocalEssentialBounds
public import HeatKernel.Moser.MeanValueSignedMatrixNestedPowers
import Mathlib.Tactic

/-! # Positive-power mean values on arbitrary nested elliptic cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The quadratic power gives a mean-value estimate on a nested cylinder with
independent spatial and lower-time gaps. A small radius fitting both gaps pays
the explicit parabolic factor. The constant is independent of every cylinder,
the small radius and the solution. No continuity or preliminary boundedness
is assumed, and the inner cylinder may reach its open top. -/
theorem exists_uniform_signed_matrix_nested_cylinder_quadratic_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a A T : ℝ) (x₀ : Fin N → ℝ) (ρ R r : ℝ),
      0 < r → r ≤ R - ρ → r ^ 2 ≤ A - a →
      ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo a T, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ R,
          isOpen_horizontalBall G hq hqpos hspan x₀ R⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo A T ×ˢ horizontalBall (G.horizontalFields hq) x₀ ρ)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / (2 : ℝ)) *
          eLpNorm v 2 (volume.restrict
            (Ioo a T ×ˢ horizontalBall (G.horizontalFields hq) x₀ R))) := by
  simpa only [ENNReal.ofReal_ofNat] using
    exists_uniform_signed_matrix_nested_cylinder_positive_power_bound
      G hq hqpos hspan hw  (p := 2) (by norm_num) ell upper hell hupper

end HeatKernel
