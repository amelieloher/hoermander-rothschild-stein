-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlMetric
public import RothschildStein.G1.WeightedSubcurves
public import RothschildStein.G1.ControlledVariation
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.H3
open G2
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- The global control-distance comparison bounds every point of an
admissible weighted curve by its control-cost radius (BB p. 22). -/
theorem controlledCurve_stays_close_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y) {δ : ℝ} {γ : ℝ → (Fin N → ℝ)}
    (hγ : isControlledCurve univ driftWeight Y δ γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (controlDistance univ driftWeight Y (γ 0) (γ t)).toReal ≤ δ := by
  have hw (i : Fin (q + 1)) : (driftWeight i : ℕ) ≤ 2 := by
    simp only [driftWeight]
    split_ifs <;> decide
  have hb := G1.controlDistance_initial_subcurve_le hw hγ ht
  rw [H.distance_eq] at hb
  have ht1 : Real.sqrt t ≤ 1 := (Real.sqrt_le_one).mpr ht.2
  have hr : Real.sqrt t * δ ≤ δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 hγ.1.le
  rw [controlDistance_toReal_of_controlNorm G H]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg t) hγ.1.le)).mp hb |>.trans hr

/-- The mean-value bound along an actual drift curve keeps the
δ² drift term and the sum of horizontal bounds (BB Theorem 1.56, p. 37). -/
theorem controlledCurve_field_sum_bound {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    {δ D : ℝ} {H : Fin q → ℝ} {γ : ℝ → (Fin N → ℝ)}
    (hγ : isControlledCurve Ω driftWeight Y δ γ)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin q,
      |fderiv ℝ f (γ t) (Y i.succ (γ t))| ≤ H i)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, |fderiv ℝ f (γ t) (Y 0 (γ t))| ≤ D) :
    |f (γ 1) - f (γ 0)| ≤ δ * (∑ i, H i) + δ ^ 2 * D := by
  apply G1.controlledCurve_variation_le hΩ hf hγ
  intro t ht
  rw [Fin.sum_univ_succ]
  simp only [driftWeight, eq_self, ite_true, show ((2 : ℕ+) : ℕ) = 2 from rfl,
    Fin.succ_ne_zero, ite_false, show ((1 : ℕ+) : ℕ) = 1 from rfl, pow_one]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hH t ht i) hγ.1.le)
  have hb := add_le_add (mul_le_mul_of_nonneg_left (hD t ht) (sq_nonneg δ)) hs
  simpa only [← Finset.mul_sum, add_comm (δ ^ 2 * D)] using hb

end RothschildStein.H3
