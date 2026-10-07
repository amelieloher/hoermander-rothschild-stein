-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoHalving
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A fixed choice of minimisers on all controlled balls.
Its value on invalid parameters is irrelevant. BB p. 328; the centers lie in the patch. -/
def campanatoConstant (P : DoublingPatch X) (u : X → ℝ) (x : X) (r : ℝ) : ℝ := by
  classical
  exact if h : IntegrableOn u P.W P.μ ∧ x ∈ P.S ∧ 0 < r ∧ r ≤ 6 * P.ρ then
    (P.exists_oscillation_minimizer h.1 h.2.1 h.2.2.1 h.2.2.2).choose else 0

/-- The chosen constant has the sole minimising property used below. -/
theorem campanatoConstant_minimizes (P : DoublingPatch X) {u : X → ℝ}
    (hu : IntegrableOn u P.W P.μ) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) (c : ℝ) :
    integralOscillation (P.μ.restrict (ball x r)) u (campanatoConstant P u x r) ≤
      integralOscillation (P.μ.restrict (ball x r)) u c := by
  classical
  rw [campanatoConstant, dite_eq_left ⟨hu, hx, hr, hrρ⟩]
  exact (P.exists_oscillation_minimizer hu hx hr hrρ).choose_spec c

/-- Uniform integral bound for the chosen minimisers. -/
theorem campanatoConstant_integral_bound (P : DoublingPatch X) {α : ℝ} {u : X → ℝ}
    (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    integralOscillation (P.μ.restrict (ball x r)) u (campanatoConstant P u x r) ≤
      (campanatoSeminorm α P u).toReal * r ^ α * (P.μ (ball x r)).toReal :=
  P.oscillation_minimizer_bound hu hx hr hrρ
    (campanatoConstant_minimizes P hu.1 hx hr hrρ)

/-- Consecutive dyadic choices satisfy BB Lemma 7.40's estimate. -/
theorem campanatoConstant_halving (P : DoublingPatch X) {α : ℝ} (hα : 0 ≤ α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    |campanatoConstant P u x r - campanatoConstant P u x (r / 2)| ≤
      (P.C_D + 1) * r ^ α * (campanatoSeminorm α P u).toReal :=
  P.campanato_halving hα hu hx hr hrρ
    (campanatoConstant_minimizes P hu.1 hx hr hrρ)
    (campanatoConstant_minimizes P hu.1 hx (by linarith) (by linarith))
end RothschildStein.H2
