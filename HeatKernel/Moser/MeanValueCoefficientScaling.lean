-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicMeasurability
import Mathlib.Tactic

/-! # Measurable elliptic coefficients under parabolic group scaling -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel

/-- Global component measurability is preserved by parabolic pullback. -/
theorem measurable_coefficients_parabolic_pullback {N q : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)) :
    ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) =>
      a (parabolicGroupHomeomorph G t₀ x₀ r hr z).1
        (parabolicGroupHomeomorph G t₀ x₀ r hr z).2 i j) :=
  fun i j => (ha i j).comp (parabolicGroupHomeomorph G t₀ x₀ r hr).measurable

/-- Symmetry and the exact lower and upper quadratic-form constants are preserved. -/
theorem ellipticity_coefficients_parabolic_pullback {N q : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ} {lower upper : ℝ}
    (ha : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a z.1 z.2 i j = a z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) :
    let T := parabolicGroupHomeomorph G t₀ x₀ r hr
    ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, a (T z).1 (T z).2 i j = a (T z).1 (T z).2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a (T z).1 (T z).2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, a (T z).1 (T z).2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2 :=
  (ae_comp_parabolicGroupHomeomorph_iff G t₀ x₀ r hr _).mpr ha

end HeatKernel
