-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierBound
public import RothschildStein.G2.GaugeConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Group mollification preserves a global Holder constant by left
invariance of the gauge distance (BB Theorem 8.52(iii), pp. 381–382). -/
theorem groupRegularize_holder_bound (ν : G2.HomogeneousNorm G)
    (φ : G2.GroupMollifier G ν) {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) {M H α : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (hholder : ∀ x y, |f x - f y| ≤ H * G2.gaugeDistance G ν x y ^ α)
    {ε : ℝ} (hε : 0 < ε) (x y : Fin N → ℝ) :
    |G2.groupRegularize G φ f ε x - G2.groupRegularize G φ f ε y| ≤
      H * G2.gaugeDistance G ν x y ^ α := by
  have hφ : Integrable φ := φ.smooth.continuous.integrable_of_hasCompactSupport φ.compact
  have hi (a : Fin N → ℝ) : Integrable
      (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) a)) volume := by
    have hm : AEStronglyMeasurable
        (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) a)) volume :=
      (φ.smooth.continuous.mul (hf.comp ((G2.continuous_mul G).comp
        (((G2.continuous_inv G).comp (G2.continuous_dilate G ε)).prodMk
          continuous_const)))).aestronglyMeasurable
    apply Integrable.mono' (hφ.mul_const M) hm
    exact Eventually.of_forall fun z => by
      rw [norm_mul, Real.norm_of_nonneg (φ.nonneg z)]
      exact mul_le_mul_of_nonneg_left (hM _) (φ.nonneg z)
  rw [G2.groupRegularize_eq_integral G φ f hε x,
    G2.groupRegularize_eq_integral G φ f hε y, ← integral_sub (hi x) (hi y)]
  change ‖∫ z, φ z * f (G.mul (G.inv (G.dilate ε z)) x) -
    φ z * f (G.mul (G.inv (G.dilate ε z)) y)‖ ≤ _
  have hb : ∀ᵐ z ∂volume,
      ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x) -
        φ z * f (G.mul (G.inv (G.dilate ε z)) y)‖ ≤
      φ z * (H * G2.gaugeDistance G ν x y ^ α) := by
    apply Eventually.of_forall
    intro z
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg z), Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg z)
    have h := hholder (G.mul (G.inv (G.dilate ε z)) x)
      (G.mul (G.inv (G.dilate ε z)) y)
    rwa [G2.gaugeDistance_leftInvariant G ν x y (G.inv (G.dilate ε z))] at h
  have hn := norm_integral_le_of_norm_le
    (hφ.mul_const (H * G2.gaugeDistance G ν x y ^ α)) hb
  simpa only [integral_mul_const, φ.integral_eq_one, one_mul] using hn

end RothschildStein.H3
