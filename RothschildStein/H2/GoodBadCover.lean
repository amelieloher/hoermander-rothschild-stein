-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.GoodBadLevelSet

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The good/bad level set has the stated measure, covering, average, and overlap bounds with explicit constants c_G and N (BB pp. 322–324). The threshold is written as ‖f‖₁/α < μ(Ω₁) in extended arithmetic, equivalently α > ‖f‖₁/μ(Ω₁). -/
theorem LocDoubling.good_bad_cover (D : LocDoubling X) {xbar : X}
    (hxbar : xbar ∈ D.Ω₀) (f : X → ℝ) (hf : IntegrableOn f D.Ω₂ D.μ)
    (hsupport : ∀ᵐ y ∂D.μ.restrict D.Ω₂, y ∉ ball xbar D.κ → f y = 0)
    {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (hthreshold : eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α < D.μ D.Ω₁) :
    let A := goodBadLevelSet D f α
    IsOpen A ∧ A ⊆ ball xbar (3 * D.κ) ∧ A ⊆ D.Ω₁ ∧
      D.μ A ≤ eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α ∧
      D.μ A < D.μ D.Ω₁ ∧
      ∃ u : Set X, u ⊆ A ∧ u.Countable ∧
        A = ⋃ z ∈ u, ball z (whitneyRadius A D.κ z) ∧
        (∀ᵐ x ∂D.μ, x ∈ D.Ω₁ \ A → ‖f x‖ₑ ≤ ENNReal.ofReal (D.C_D ^ 3 * α)) ∧
        (∀ z ∈ u, (⨍⁻ y in ball z (whitneyRadius A D.κ z), ‖f y‖ₑ ∂D.μ) ≤
          ENNReal.ofReal (goodAverageConstant D m * α)) ∧
        (∑' z : u, D.μ (ball (z : X) (whitneyRadius A D.κ z))) ≤
          ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5) *
            (eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α) ∧
        (∀ x : X, (∑' z : X, if z ∈ u ∧ x ∈ ball z (whitneyRadius A D.κ z)
          then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5)) ∧
        (∀ z ∈ u, 0 < whitneyRadius A D.κ z ∧ 5 * whitneyRadius A D.κ z ≤ D.κ) ∧
        (∀ z ∈ u, ball z (5 * whitneyRadius A D.κ z) ⊆ D.Ω₁) ∧
        (∀ x : X, {z ∈ u | x ∈ ball z (whitneyRadius A D.κ z)}.Finite) := by
  let A := goodBadLevelSet D f α
  have ht : 0 < ENNReal.ofReal (D.C_D ^ 3 * α) :=
    ENNReal.ofReal_pos.mpr (mul_pos (pow_pos (by linarith [D.one_lt_C_D]) _) hα)
  have hA : IsOpen A := isOpen_patchMaximal_superlevel D.μ D.Ω₁ D.κ f _
  have hloc : A ⊆ ball xbar (3 * D.κ) := D.maximal_superlevel_location hxbar f hsupport ht
  have hA₁ : A ⊆ D.Ω₁ := D.maximal_superlevel_subset_inner hxbar f hsupport ht
  have hμA := D.good_bad_level_measure f hf hα
  have hsmall : D.μ A < D.μ D.Ω₁ := hμA.trans_lt hthreshold
  have hne : Aᶜ.Nonempty := by
    by_contra hn
    have hsub : D.Ω₁ ⊆ A := by
      intro x _
      by_contra hx
      exact hn ⟨x, hx⟩
    exact hsmall.not_ge (measure_mono hsub)
  have hmass : eLpNorm f 1 (D.μ.restrict D.Ω₂) ≤ ENNReal.ofReal α * D.μ D.Ω₁ := by
    have hh := (ENNReal.div_le_iff (by positivity : ENNReal.ofReal α ≠ 0)
      ENNReal.ofReal_ne_top).mp hthreshold.le
    simpa only [mul_comm] using hh
  obtain ⟨u, hu, huc, hcov, hover, hr, _hi, _hs, hfin⟩ := D.whitney_covering hA hA₁ hne
  have hgood : ∀ᵐ x ∂D.μ, x ∈ D.Ω₁ \ A → ‖f x‖ₑ ≤ ENNReal.ofReal (D.C_D ^ 3 * α) := by
    filter_upwards [D.good_set_bound_of_maximal_weak_type D.outer_maximal_weak_type f hf
      (ENNReal.ofReal (D.C_D ^ 3 * α))] with x hx hxs
    exact hx hxs.1 hxs.2
  have hsum := sum_ball_measure_le_overlap D.μ hA.measurableSet huc
    (whitneyRadius A D.κ) (ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5))
    (fun z hz => whitney_ball_subset hA hne D.κ_pos (hu hz)) hover
  refine ⟨hA, hloc, hA₁, hμA, hsmall, u, hu, huc, hcov, hgood,
    fun z hz => D.whitney_good_average hxbar f hf hsupport hα hm hml hmass hne (hu hz),
    hsum.trans (mul_le_mul_right hμA _), hover, hr, ?_, hfin⟩
  intro z hz y hy
  have hzy : dist y z < 5 * whitneyRadius A D.κ z := mem_ball.mp hy
  have hzbar : dist z xbar < 3 * D.κ := mem_ball.mp (hloc (hu hz))
  apply D.incl₀ xbar hxbar
  rw [mem_closedBall]
  linarith [dist_triangle y z xbar, (hr z hz).2, D.κ_pos]

end RothschildStein.H2
