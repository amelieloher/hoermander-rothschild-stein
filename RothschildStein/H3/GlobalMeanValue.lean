-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlCurveBounds
public import RothschildStein.G1.DistanceVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.H3
open G2
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- Under the global control-norm comparison, the mean-value estimate
has the horizontal sum and d² drift factors (BB p. 37). -/
theorem global_meanValue_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {D : ℝ} {M : Fin q → ℝ}
    (hM : ∀ z, ∀ i : Fin q, |fderiv ℝ f z (Y i.succ z)| ≤ M i)
    (hD : ∀ z, |fderiv ℝ f z (Y 0 z)| ≤ D) (x y : Fin N → ℝ) :
    |f y - f x| ≤ (controlDistance univ driftWeight Y x y).toReal * (∑ i, M i) +
      (controlDistance univ driftWeight Y x y).toReal ^ 2 * D := by
  have hM0 : 0 ≤ ∑ i, M i := Finset.sum_nonneg (fun i _ =>
    (abs_nonneg _).trans (hM x i))
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x)
  have hfinite : controlDistance univ driftWeight Y x y ≠ ⊤ := by
    rw [H.distance_eq]
    exact ENNReal.ofReal_ne_top
  apply G1.variation_le_controlDistance_of_curve_bound hfinite
    (fun δ => δ * (∑ i, M i) + δ ^ 2 * D) (by fun_prop)
  · intro a ha b _ hab
    exact add_le_add (mul_le_mul_of_nonneg_right hab hM0)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hD0)
  · intro δ γ hγ hγ0 hγ1
    have hb := controlledCurve_field_sum_bound isOpen_univ hf.contDiffOn hγ
      (fun t _ i => hM (γ t) i) (fun t _ => hD (γ t))
    simpa only [hγ0, hγ1] using hb

end RothschildStein.H3
