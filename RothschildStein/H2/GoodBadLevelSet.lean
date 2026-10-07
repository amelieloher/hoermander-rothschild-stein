-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.GoodBadAverages
public import RothschildStein.H2.CoverMass

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The whole-space bad set for the good/bad decomposition, defined using the maximal function on Ω₁. -/
def goodBadLevelSet (D : LocDoubling X) (f : X → ℝ) (α : ℝ) : Set X :=
  {x | ENNReal.ofReal (D.C_D ^ 3 * α) < patchMaximal D.μ D.Ω₁ D.κ f x}

/-- The explicit good-average constant c_G. -/
def goodAverageConstant (D : LocDoubling X) (m : ℝ) : ℝ :=
  max (D.C_D ^ 6) (D.C_D ^ 3 * (D.μ D.Ω₁).toReal / m)

/-- The C_D cubed in the level threshold cancels the exact
weak-type constant; no extra doubling factor survives (BB pp. 323–324). -/
theorem LocDoubling.good_bad_level_measure (D : LocDoubling X) (f : X → ℝ)
    (hf : IntegrableOn f D.Ω₂ D.μ) {α : ℝ} (hα : 0 < α) :
    D.μ (goodBadLevelSet D f α) ≤ eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α := by
  have hC : 0 < D.C_D := by linarith [D.one_lt_C_D]
  have hC₃ : 0 < D.C_D ^ 3 := pow_pos hC _
  have hw := D.outer_maximal_weak_type f hf (D.C_D ^ 3 * α) (mul_pos hC₃ hα)
  have he : (ENNReal.ofReal D.C_D ^ 3 / ENNReal.ofReal (D.C_D ^ 3 * α)) *
      eLpNorm f 1 (D.μ.restrict D.Ω₂) =
      eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α := by
    rw [ENNReal.ofReal_mul hC₃.le, ENNReal.ofReal_pow hC.le,
      div_eq_mul_inv, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl (by finiteness)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by positivity) (by finiteness)]
    simp only [mul_one, div_eq_mul_inv, mul_comm]
  exact hw.trans_eq he

/-- Both capped and stopping balls satisfy the single explicit
c_G average estimate (BB Lemma 7.34, p. 323). -/
theorem LocDoubling.whitney_good_average (D : LocDoubling X) {xbar : X}
    (hxbar : xbar ∈ D.Ω₀) (f : X → ℝ) (hf : IntegrableOn f D.Ω₂ D.μ)
    (hsupport : ∀ᵐ y ∂D.μ.restrict D.Ω₂, y ∉ ball xbar D.κ → f y = 0)
    {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (hmass : eLpNorm f 1 (D.μ.restrict D.Ω₂) ≤ ENNReal.ofReal α * D.μ D.Ω₁)
    (hne : (goodBadLevelSet D f α)ᶜ.Nonempty)
    {z : X} (hz : z ∈ goodBadLevelSet D f α) :
    (⨍⁻ y in ball z (whitneyRadius (goodBadLevelSet D f α) D.κ z), ‖f y‖ₑ ∂D.μ) ≤
      ENNReal.ofReal (goodAverageConstant D m * α) := by
  let A := goodBadLevelSet D f α
  have ht : 0 < ENNReal.ofReal (D.C_D ^ 3 * α) := by
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (pow_pos (by linarith [D.one_lt_C_D]) _) hα
  have hA : IsOpen A := isOpen_patchMaximal_superlevel D.μ D.Ω₁ D.κ f _
  have hz₁ : z ∈ D.Ω₁ := D.maximal_superlevel_subset_inner hxbar f hsupport ht hz
  have hr := whitneyRadius_pos_le hA hne D.κ_pos hz
  rcases whitney_stopping_point hA hne D.κ_pos hz with hcap | ⟨y, hy, hzy⟩
  · rw [hcap]
    apply (D.capped_ball_average f hf hz₁ hm hα.le (hml z hz₁) hmass).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hα.le
  · have hyM : patchMaximal D.μ D.Ω₁ D.κ f y ≤ ENNReal.ofReal (D.C_D ^ 3 * α) :=
      le_of_not_gt hy
    have hb := D.stopping_ball_average f hz₁ hr.1 (by linarith [hr.2])
      (by simpa [dist_comm] using hzy) hyM
    have hC : 0 ≤ D.C_D ^ 3 := pow_nonneg (by linarith [D.one_lt_C_D]) _
    have he : ENNReal.ofReal D.C_D ^ 3 * ENNReal.ofReal (D.C_D ^ 3 * α) =
        ENNReal.ofReal (D.C_D ^ 6 * α) := by
      rw [← ENNReal.ofReal_pow (by linarith [D.one_lt_C_D]), ← ENNReal.ofReal_mul hC]
      congr 1
      ring
    rw [he] at hb
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le))

end RothschildStein.H2
