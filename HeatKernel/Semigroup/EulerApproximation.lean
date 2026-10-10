-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScalarMultipliers
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Uniform scalar Euler approximation

Quantitative logarithmic estimates control the implicit Euler approximation on bounded
intervals. Bernoulli's inequality controls the remaining half-line uniformly in the step count.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace HeatKernel

/-- The scalar implicit Euler approximation to the negative exponential. -/
def eulerMultiplier (n : ℕ) (x : ℝ) : ℝ := ((1 + x / (n : ℝ)) ^ n)⁻¹

theorem sub_sq_div_two_le_log_one_add {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 2 / 2 ≤ Real.log (1 + y) := by
  have hd : 0 < y + 2 := by positivity
  calc
    y - y ^ 2 / 2 ≤ 2 * y / (y + 2) := by
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg hy (sq_nonneg y)]
    _ ≤ Real.log (1 + y) := Real.le_log_one_add_of_nonneg hy

theorem eulerMultiplier_eq_exp {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    eulerMultiplier n x = Real.exp (-(n : ℝ) * Real.log (1 + x / (n : ℝ))) := by
  have hp : 0 < 1 + x / (n : ℝ) := by positivity
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp]
  rfl

theorem exp_neg_le_eulerMultiplier {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ eulerMultiplier n x := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (1 + x / (n : ℝ)) ≤ x / (n : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + x / (n : ℝ) by positivity)
  have hmul := mul_le_mul_of_nonneg_left hlog hn'.le
  have hcancel : (n : ℝ) * (x / (n : ℝ)) = x := by field_simp
  rw [hcancel] at hmul
  rw [eulerMultiplier_eq_exp hx]
  exact Real.exp_le_exp.mpr (by linarith)

theorem eulerMultiplier_le_exp {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    eulerMultiplier n x ≤ Real.exp (-x + x ^ 2 / (2 * (n : ℝ))) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog := sub_sq_div_two_le_log_one_add (div_nonneg hx hn'.le)
  have hmul := mul_le_mul_of_nonneg_left hlog hn'.le
  have hcancel : (n : ℝ) * (x / (n : ℝ) - (x / (n : ℝ)) ^ 2 / 2) =
      x - x ^ 2 / (2 * (n : ℝ)) := by field_simp
  rw [hcancel] at hmul
  rw [eulerMultiplier_eq_exp hx]
  exact Real.exp_le_exp.mpr (by linarith)

theorem eulerMultiplier_sub_exp_le {n : ℕ} (hn : 0 < n) {x M : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) M) :
    eulerMultiplier n x - Real.exp (-x) ≤ Real.exp (M ^ 2 / (2 * (n : ℝ))) - 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 ≤ x ^ 2 / (2 * (n : ℝ)) := by positivity
  have hexp : 0 ≤ Real.exp (x ^ 2 / (2 * (n : ℝ))) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hq)
  calc
    eulerMultiplier n x - Real.exp (-x) ≤
        Real.exp (-x) * (Real.exp (x ^ 2 / (2 * (n : ℝ))) - 1) := by
      have h := eulerMultiplier_le_exp hn hx.1
      rw [Real.exp_add] at h
      nlinarith
    _ ≤ Real.exp (x ^ 2 / (2 * (n : ℝ))) - 1 := by
      simpa using mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.1)) hexp
    _ ≤ Real.exp (M ^ 2 / (2 * (n : ℝ))) - 1 := by
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [hx.1, hx.2]

theorem eulerMultiplier_le_one_div {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    eulerMultiplier n x ≤ 1 / (1 + x) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ x / (n : ℝ) from le_trans (by norm_num) (div_nonneg hx hn'.le)) n
  have hcancel : (n : ℝ) * (x / (n : ℝ)) = x := by field_simp
  rw [hcancel] at hbern
  have hd : 0 < 1 + x := by positivity
  have hp : 0 < (1 + x / (n : ℝ)) ^ n := by positivity
  simpa only [eulerMultiplier, one_div] using (inv_le_inv₀ hp hd).mpr hbern

theorem tendstoUniformlyOn_eulerMultiplier :
    TendstoUniformlyOn eulerMultiplier (fun x => Real.exp (-x)) atTop (Ici (0 : ℝ)) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let M := 1 / ε
  have hM : 0 < M := one_div_pos.mpr hε
  have htail : 1 / (1 + M) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < 1 + M)).mpr
    have hcancel : ε * M = 1 := by dsimp [M]; field_simp
    nlinarith
  have hden : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hq := hden.const_div_atTop (M ^ 2)
  have herr : Tendsto (fun n : ℕ => Real.exp (M ^ 2 / (2 * (n : ℝ))) - 1)
      atTop (𝓝 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp hq).sub_const 1
  filter_upwards [herr.eventually_lt_const hε, eventually_gt_atTop 0] with n hsmall hn
  intro x hx
  change 0 ≤ x at hx
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
    (exp_neg_le_eulerMultiplier hn hx))]
  by_cases hxM : x ≤ M
  · exact (eulerMultiplier_sub_exp_le hn ⟨hx, hxM⟩).trans_lt hsmall
  · have hMx : M ≤ x := (not_le.mp hxM).le
    have hdiv : 1 / (1 + x) ≤ 1 / (1 + M) := by
      simpa only [one_div] using
        (inv_le_inv₀ (show 0 < 1 + x by positivity) (show 0 < 1 + M by positivity)).mpr
          (by linarith)
    exact ((sub_le_self _ (Real.exp_pos _).le).trans
      ((eulerMultiplier_le_one_div hn hx).trans hdiv)).trans_lt htail

/-- The scalar power of the resolvent multiplier with time step `t / n`. -/
def implicitEulerMultiplier (t : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  resolventMultiplier (t / (n : ℝ)) r ^ n

theorem implicitEulerMultiplier_eq_eulerMultiplier {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hrpos : 0 < r) :
    implicitEulerMultiplier t n r = eulerMultiplier n (t * (r⁻¹ - 1)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ t * (r⁻¹ - 1) :=
    mul_nonneg ht.le (sub_nonneg.mpr ((one_le_inv₀ hrpos).mpr hr.2))
  have hd := (resolventMultiplier_denominator_pos (div_pos ht hn') hr).ne'
  have hb : 1 + t * (r⁻¹ - 1) / (n : ℝ) ≠ 0 := by positivity
  have heq : resolventMultiplier (t / (n : ℝ)) r =
      (1 + t * (r⁻¹ - 1) / (n : ℝ))⁻¹ := by
    unfold resolventMultiplier
    field_simp
  simp only [implicitEulerMultiplier, eulerMultiplier, heq, inv_pow]

theorem tendstoUniformlyOn_implicitEulerMultiplier {t : ℝ} (ht : 0 < t) :
    TendstoUniformlyOn (implicitEulerMultiplier t) (heatMultiplier t) atTop
      (Icc (0 : ℝ) 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := Metric.tendstoUniformlyOn_iff.mp tendstoUniformlyOn_eulerMultiplier ε hε
  filter_upwards [h, eventually_gt_atTop 0] with n hbound hn
  intro r hr
  rcases eq_or_lt_of_le hr.1 with hrzero | hrpos
  · rw [← hrzero]
    simpa [implicitEulerMultiplier, hn.ne'] using hε
  · rw [heatMultiplier_of_pos ht hrpos,
      implicitEulerMultiplier_eq_eulerMultiplier ht hn hr hrpos]
    simpa only [neg_mul] using hbound (t * (r⁻¹ - 1))
      (mul_nonneg ht.le (sub_nonneg.mpr ((one_le_inv₀ hrpos).mpr hr.2)))

end HeatKernel
