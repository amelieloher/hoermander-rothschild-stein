-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GaugeWordBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The drift derivative of the smooth gauge is of degree minus one. -/
theorem gauge_driftDerivative_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, x ≠ 0 →
      |fieldDerivative (H.fields 0) ν x| ≤ M / ν x := by
  obtain ⟨M, hM, hb⟩ := gauge_wordDerivative_bound G H ν hν [0]
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hh := hb x hx
  norm_num [wordDerivative, H1.differentialWordWeight] at hh
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hh

/-- Ordered second horizontal derivatives of the gauge have the
same degree minus one bound, retaining the order of the field actions. -/
theorem gauge_secondHorizontalDerivative_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (i j : Fin q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, x ≠ 0 →
      |fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) ν) x| ≤ M / ν x := by
  obtain ⟨M, hM, hb⟩ := gauge_wordDerivative_bound G H ν hν [i.succ, j.succ]
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hh := hb x hx
  norm_num [wordDerivative, H1.differentialWordWeight, Fin.succ_ne_zero] at hh
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hh

end RothschildStein.H3
