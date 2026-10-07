-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WhitneyOverlap

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Whitney covering with clauses (a)–(d), overlap constant C_D⁷+C_D⁵, and pointwise finite selected balls (BB Lemma 7.33, pp. 321–322). The radii are capped at κ/5. -/
theorem LocDoubling.whitney_covering (D : LocDoubling X) {A : Set X}
    (hA : IsOpen A) (hA₁ : A ⊆ D.Ω₁) (hne : Aᶜ.Nonempty) :
    ∃ u : Set X, u ⊆ A ∧ u.Countable ∧
      A = ⋃ x ∈ u, ball x (whitneyRadius A D.κ x) ∧
      (∀ x : X, (∑' z : X, if z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)
        then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5)) ∧
      (∀ z ∈ u, 0 < whitneyRadius A D.κ z ∧ 5 * whitneyRadius A D.κ z ≤ D.κ) ∧
      (∀ z ∈ u, ball z (4 * whitneyRadius A D.κ z) ⊆ D.Ω₂) ∧
      (∀ z ∈ u, whitneyRadius A D.κ z = D.κ / 5 ∨
        ∃ y ∉ A, dist z y < 4 * whitneyRadius A D.κ z) ∧
      (∀ x : X, {z ∈ u | x ∈ ball z (whitneyRadius A D.κ z)}.Finite) := by
  obtain ⟨u, hu, hc, hd, hcov, hr, hi, hs⟩ := D.whitney_selection hA hA₁ hne
  exact ⟨u, hu, hc, hcov, D.whitney_overlap_sum hA hne hu hA₁ hd,
    hr, hi, hs, D.whitney_overlap_finite hA hne hu hA₁ hd⟩

end RothschildStein.H2
