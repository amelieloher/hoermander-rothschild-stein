-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.DualTruncatedBound

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Monotone convergence upgrades the bounded dual tests to
Lᵖ membership and the full norm estimate (BB p. 326). -/
theorem lp_bound_of_l2_pairing (μ : Measure X) [IsFiniteMeasure μ]
    (F : Lp ℝ 2 μ) {p q H : ℝ} (hp : 1 < p) (hq : 0 < q) (hH : 0 ≤ H)
    (hpq : (p - 1) * q = p) (hrecip : 1 / p + 1 / q = 1)
    (hpair : ∀ w : Lp ℝ 2 μ, MemLp w (ENNReal.ofReal q) μ →
      |∫ x, F x * w x ∂μ| ≤ H * (eLpNorm w (ENNReal.ofReal q) μ).toReal) :
    MemLp F (ENNReal.ofReal p) μ ∧ eLpNorm F (ENNReal.ofReal p) μ ≤ ENNReal.ofReal H := by
  have hp0 : 0 < p := by linarith
  have hFm := (Lp.stronglyMeasurable F).measurable
  have hmeas : ∀ n : ℕ, AEMeasurable (fun x => ENNReal.ofReal ((min |F x| (n : ℝ)) ^ p)) μ := by
    intro n
    exact ((by simpa only [Real.norm_eq_abs] using hFm.norm.min measurable_const :
      Measurable (fun x => min |F x| (n : ℝ))).pow_const p).ennreal_ofReal.aemeasurable
  have hmono : ∀ᵐ x ∂μ, Monotone fun n : ℕ => ENNReal.ofReal ((min |F x| (n : ℝ)) ^ p) :=
    Eventually.of_forall fun x i j hij => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (le_min (abs_nonneg _) (Nat.cast_nonneg i))
        (min_le_min_left _ (Nat.cast_le.mpr hij)) hp0.le)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => ENNReal.ofReal ((min |F x| (n : ℝ)) ^ p))
      atTop (𝓝 (ENNReal.ofReal (|F x| ^ p))) := by
    apply Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |F x|
    have heq : (fun n : ℕ => ENNReal.ofReal ((min |F x| (n : ℝ)) ^ p)) =ᶠ[atTop]
        fun _ => ENNReal.ofReal (|F x| ^ p) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [min_eq_left (hN.trans (Nat.cast_le.mpr hn))]
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have hM : moment μ p F ≤ ENNReal.ofReal (H ^ p) := by
    apply le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim)
    apply Eventually.of_forall
    intro n
    have hn := truncated_moment_le_of_pairing μ F hp hq hH hpq hrecip hpair (Nat.cast_nonneg n)
    have hg : ∀ x, (0 : ℝ) ≤ min |F x| (n : ℝ) := fun x => le_min (abs_nonneg _) (Nat.cast_nonneg n)
    simpa only [moment, abs_of_nonneg (hg _)] using hn
  have hmem := (memLp_iff_moment_lt_top μ hFm.aemeasurable hp0).mpr
    (hM.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hmem, ?_⟩
  rw [eLpNorm_eq_moment_rpow μ hFm.aemeasurable hp0]
  calc
    _ ≤ ENNReal.ofReal (H ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hM (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hH hp0.le, ← ENNReal.rpow_mul,
        show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]

end RothschildStein.H2
