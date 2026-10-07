-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierSubstitution
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Bounded uniformly continuous data converge uniformly under
ordinary mollification (BB Lemma 2.8, pp. 72–73; uniform version). -/
theorem tendstoUniformly_euclideanRegularize_of_uniformContinuous
    (hn : 0 < n) {f : (Fin n → ℝ) → ℝ} (hf : UniformContinuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    TendstoUniformly (fun ε : ℝ => euclideanRegularize n f ε) f (𝓝[>] 0) := by
  have hJ : Integrable (euclideanJ n) volume := (euclideanJ_smooth_compact n).1.continuous.integrable_of_hasCompactSupport
    (euclideanJ_smooth_compact n).2
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hf (η/2) (half_pos hη)
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε x
  have ht : Continuous (fun y : Fin n → ℝ => x-ε • y) :=
    (continuous_const (y := x)).sub (continuous_id.const_smul ε)
  have hc : Continuous (fun y => euclideanJ n y * f (x-ε • y)) := by
    exact (euclideanJ_smooth_compact n).1.continuous.mul (hf.continuous.comp ht)
  have hm : AEStronglyMeasurable
      (fun y => euclideanJ n y * f (x-ε • y)) volume := hc.aestronglyMeasurable
  have hi : Integrable (fun y => euclideanJ n y * f (x-ε • y)) volume :=
    Integrable.mono' (hJ.mul_const C) hm (Eventually.of_forall fun y => by
      rw [norm_mul,Real.norm_of_nonneg ((euclideanJ_normalized n).1 y)]
      exact mul_le_mul_of_nonneg_left (hC _) ((euclideanJ_normalized n).1 y))
  have hb : ∀ᵐ y ∂volume,
      ‖euclideanJ n y * (f (x-ε • y)-f x)‖ ≤ euclideanJ n y * (η/2) := by
    apply Eventually.of_forall
    intro y
    by_cases hy : ‖y‖ < 1/2
    · rw [norm_mul,Real.norm_of_nonneg ((euclideanJ_normalized n).1 y)]
      apply mul_le_mul_of_nonneg_left _ ((euclideanJ_normalized n).1 y)
      have hxy : dist (x-ε • y) x < δ := by
        rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,
          Real.norm_of_nonneg hε.1.le]
        have he : ε * ‖y‖ < ε := by
          exact mul_lt_of_lt_one_right hε.1 (hy.trans (by norm_num))
        exact he.trans hε.2
      simpa only [dist_eq_norm] using (hd hxy).le
    · rw [euclideanJ_vanish y (le_of_not_gt hy)]
      simp only [MulZeroClass.zero_mul,norm_zero,le_refl]
  have he : euclideanRegularize n f ε x-f x =
      ∫ y, euclideanJ n y * (f (x-ε • y)-f x) := by
    rw [euclideanRegularize_eq_integral_sub hn f hε.1 x]
    simp only [mul_sub]
    rw [integral_sub hi (hJ.mul_const (f x)),integral_mul_const,
      (euclideanJ_normalized n).2,one_mul]
  have H := norm_integral_le_of_norm_le (hJ.mul_const (η/2)) hb
  rw [integral_mul_const,(euclideanJ_normalized n).2,one_mul,← he] at H
  rw [dist_eq_norm,norm_sub_rev]
  exact H.trans_lt (half_lt_self hη)

end RothschildStein.S
