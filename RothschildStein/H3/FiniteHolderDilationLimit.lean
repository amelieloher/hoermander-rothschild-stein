-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightedHolderDilation
public import RothschildStein.H3.HolderSeminormScalingENNReal
public import Mathlib.Basic.ENNReal.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- A finite weighted family of actual quadratic dilates
passes from full-norm bounds to a support-independent seminorm bound.
The dilated bounds are explicit; BB Corollary 8.51, p. 380. -/
theorem finite_holder_seminorm_bound_of_dilated_norm_bounds {N : ℕ}
    {J : Type*} [Fintype J] (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (a : ℝ≥0) (ha : 0 < (a : ℝ)) (R0 : ℝ) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (weight : J → ℝ≥0∞) (hw : ∀ j, weight j ≠ ⊤)
    (u : J → ControlCarrier N → ℝ) (F : ControlCarrier N → ℝ) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    (∀ j, H2.BoundedHolder a univ (u j)) → H2.BoundedHolder a univ F →
    (∀ R : ℝ, R0 ≤ R → 0 < R →
      (∑ j, weight j * @H2.boundedHolderNorm (ControlCarrier N) metric a univ
        (fun x : ControlCarrier N => R ^ 2 * u j (G.dilate R x))) ≤
      c * @H2.boundedHolderNorm (ControlCarrier N) metric a univ
        (fun x : ControlCarrier N => R ^ 2 * F (G.dilate R x))) →
    (∑ j, weight j * H2.holderSemi a univ (u j)) ≤
      c * H2.holderSemi a univ F := by
  classical
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hu hF hscale
  let A := ∑ j, weight j * H2.holderSup univ (u j)
  let B := ∑ j, weight j * H2.holderSemi a univ (u j)
  have hA : A ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun j _ =>
    ENNReal.mul_ne_top (hw j) (hu j).parts.1.ne)
  have hB : B ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun j _ =>
    ENNReal.mul_ne_top (hw j) (hu j).parts.2.ne)
  rw [← ENNReal.ofReal_toReal hc]
  apply holder_seminorm_bound_of_scaled_ennreal_full_norm_bound ha
    ENNReal.toReal_nonneg hA hB hF.parts.1.ne hF.parts.2.ne
  intro R hR hp
  rw [ENNReal.ofReal_toReal hc]
  have hh := hscale R hR hp
  have hn (j : J) := weighted_holderNorm_dilate G ν h1 hsym hp 2 a (u j) (hu j).parts.2
  have hnF := weighted_holderNorm_dilate G ν h1 hsym hp 2 a F hF.parts.2
  simp only [Real.rpow_two] at hn hnF
  simp_rw [hn, hnF] at hh
  have he : (∑ j, weight j * (ENNReal.ofReal (R ^ 2) *
      (H2.holderSup univ (u j) + ENNReal.ofReal (R ^ (a : ℝ)) * H2.holderSemi a univ (u j)))) =
      ENNReal.ofReal (R ^ 2) * (A + ENNReal.ofReal (R ^ (a : ℝ)) * B) := by
    dsimp only [A, B]
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    apply congrArg₂ (fun x y : ℝ≥0∞ => x + y)
    · apply Finset.sum_congr rfl
      intro j _
      ac_rfl
    · apply Finset.sum_congr rfl
      intro j _
      ac_rfl
  rw [he] at hh
  have hcR : c * (ENNReal.ofReal (R ^ 2) *
      (H2.holderSup univ F + ENNReal.ofReal (R ^ (a : ℝ)) * H2.holderSemi a univ F)) =
      ENNReal.ofReal (R ^ 2) * (c *
      (H2.holderSup univ F + ENNReal.ofReal (R ^ (a : ℝ)) * H2.holderSemi a univ F)) := by
    ac_rfl
  rw [hcR] at hh
  exact (ENNReal.mul_le_mul_iff_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hp 2))) ENNReal.ofReal_ne_top).mp hh

end RothschildStein.H3
