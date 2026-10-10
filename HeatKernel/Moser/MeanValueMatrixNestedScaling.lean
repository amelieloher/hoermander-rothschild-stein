-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueMatrixPositivePowers
public import HeatKernel.Moser.MeanValueSignedMatrixNestedScaling
import Mathlib.Tactic

/-! # Normalized elliptic matrix mean values for arbitrary fixed cylinder shapes -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Every fixed positive aspect ratio and strictly smaller inner time and radius
factors give a normalized mean-value estimate for every fixed positive power.
The constant is independent of the center, scale, top time and nonnegative uniformly elliptic matrix weak solution. Both cylinders share the open top. -/
theorem exists_uniform_matrix_nested_cylinder_positive_power_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p τ θ ρ : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hθτ : θ < τ) (hρone : ρ < 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict
        (Ioo (t₀ - r ^ 2 * τ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r), 0 ≤ v z) →
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t₀ - r ^ 2 * τ) t₀, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ r,
          isOpen_horizontalBall G hq hqpos hspan x₀ r⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo (t₀ - r ^ 2 * θ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r * ρ))) ≤
        ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p)
          (((volume : Measure (ℝ × (Fin N → ℝ)))
            (Ioo (t₀ - r ^ 2 * τ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r))⁻¹ •
              volume.restrict (Ioo (t₀ - r ^ 2 * τ) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r)) := by
  obtain ⟨C, hC, hmean⟩ := exists_uniform_signed_matrix_nested_cylinder_positive_power_mean_value
    G hq hqpos hspan hw hp hτ hθτ hρone ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro t₀ x₀ r hr v coeff _hv0 hweak ha hbound
  exact hmean t₀ x₀ r hr v coeff hweak ha hbound

end HeatKernel
