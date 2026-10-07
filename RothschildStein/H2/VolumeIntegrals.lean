-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.AnnularIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2

/-- The explicit geometric-series constant in BB Lemma 7.5, p. 297. -/
def volumeIntegralConstant (C β : ℝ) : ℝ := C / (1 - (2 : ℝ) ^ (-β))

private theorem inner_power {r : ℝ} (hr : 0 < r) (β : ℝ) (n : ℕ) :
    (r / 2 ^ n) ^ β = r ^ β * ((2 : ℝ) ^ (-β)) ^ n := by
  rw [Real.div_rpow hr.le (by positivity), ← Real.rpow_natCast_mul (by norm_num),
    mul_comm (n : ℝ) β, Real.rpow_mul_natCast (by norm_num), div_eq_mul_inv,
    ← inv_pow, ← Real.rpow_neg (by norm_num)]

private theorem outer_power {r : ℝ} (hr : 0 < r) (β : ℝ) (n : ℕ) :
    ((2 : ℝ) ^ n * r) ^ (-β) = r ^ (-β) * ((2 : ℝ) ^ (-β)) ^ n := by
  rw [Real.mul_rpow (by positivity) hr.le, ← Real.rpow_natCast_mul (by norm_num),
    mul_comm (n : ℝ) (-β), Real.rpow_mul_natCast (by norm_num), mul_comm]

private theorem geometric_sum {C t β : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (hβ : 0 < β) :
    (∑' n : ℕ, ENNReal.ofReal (t * ((2 : ℝ) ^ (-β)) ^ n) * ENNReal.ofReal C) =
      ENNReal.ofReal (volumeIntegralConstant C β * t) := by
  have hq : 0 < (2 : ℝ) ^ (-β) := Real.rpow_pos_of_pos (by norm_num) _
  have hql : (2 : ℝ) ^ (-β) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  simp only [ENNReal.ofReal_mul ht, ENNReal.ofReal_pow hq.le]
  simp_rw [mul_right_comm _ _ (ENNReal.ofReal C)]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hq.le,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hql), ← ENNReal.ofReal_mul ht,
    ← ENNReal.ofReal_mul (mul_nonneg ht hC)]
  congr 1
  unfold volumeIntegralConstant
  ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Inner volume integral with the explicit constant and full patch range.
The nonnegative integral excludes the null diagonal, as in BB Lemma 7.5, p. 297. -/
theorem DoublingPatch.inner_volume_integral (P : DoublingPatch X) {z : X}
    (hz : z ∈ P.S) {β r : ℝ} (hβ : 0 < β) (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    (∫⁻ y in ball z r \ {z}, ENNReal.ofReal ((dist z y) ^ β) *
      (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
      ENNReal.ofReal (volumeIntegralConstant P.C_D β * r ^ β) := by
  let A : ℕ → Set X := fun n => {y | r / 2 ^ (n + 1) ≤ dist z y ∧ dist z y < r / 2 ^ n}
  have hcover : ball z r \ {z} ⊆ ⋃ n, A n := by
    intro y hy
    have hd : 0 < dist z y := dist_pos.mpr (by simpa [eq_comm] using hy.2)
    obtain ⟨n, hn⟩ := exists_inner_dyadic hd (by simpa [mem_ball, dist_comm] using hy.1)
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hA (n : ℕ) :
      (∫⁻ y in A n, ENNReal.ofReal ((dist z y) ^ β) * (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
        ENNReal.ofReal (r ^ β * ((2 : ℝ) ^ (-β)) ^ n) * ENNReal.ofReal P.C_D := by
    rw [← inner_power hr β n]
    apply P.weighted_annulus hz (by positivity)
      ((div_le_self hr.le (one_le_pow₀ (by norm_num))).trans hrρ)
      (by rw [pow_succ, div_mul_eq_div_div]; ring_nf; rfl)
    intro y _ hy
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow dist_nonneg hy.le hβ.le)
  calc
    _ ≤ ∫⁻ y in ⋃ n, A n, ENNReal.ofReal ((dist z y) ^ β) * (volumeAt P.μ z y)⁻¹ ∂P.μ :=
      lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
    _ ≤ ∑' n, ∫⁻ y in A n, ENNReal.ofReal ((dist z y) ^ β) * (volumeAt P.μ z y)⁻¹ ∂P.μ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (r ^ β * ((2 : ℝ) ^ (-β)) ^ n) * ENNReal.ofReal P.C_D :=
      ENNReal.tsum_le_tsum hA
    _ = _ := geometric_sum (by linarith [P.one_lt_C_D]) (Real.rpow_nonneg hr.le _) hβ

/-- Outer volume integral; truncation of the last annulus costs one
rather than two doubling factors (BB Lemma 7.5, p. 297). -/
theorem DoublingPatch.outer_volume_integral (P : DoublingPatch X) {z : X}
    (hz : z ∈ P.S) {β r σ : ℝ} (hβ : 0 < β) (hr : 0 < r)
    (_hrσ : r ≤ σ) (hσρ : σ ≤ 6 * P.ρ) :
    (∫⁻ y in ball z σ \ ball z r, ENNReal.ofReal ((dist z y) ^ (-β)) *
      (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
      ENNReal.ofReal (volumeIntegralConstant P.C_D β * r ^ (-β)) := by
  let A : ℕ → Set X := fun n =>
    {y | 2 ^ n * r ≤ dist z y ∧ dist z y < min (2 ^ (n + 1) * r) σ}
  have hcover : ball z σ \ ball z r ⊆ ⋃ n, A n := by
    intro y hy
    have hd : r ≤ dist z y := by simpa [mem_ball, dist_comm, not_lt] using hy.2
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hr).mpr (by simpa using hd))
      (by norm_num : (1 : ℝ) < 2)
    refine mem_iUnion.mpr ⟨n, ?_, lt_min ?_ ?_⟩
    · exact (le_div_iff₀ hr).mp hn
    · exact (div_lt_iff₀ hr).mp hn'
    · simpa [mem_ball, dist_comm] using hy.1
  have hA (n : ℕ) :
      (∫⁻ y in A n, ENNReal.ofReal ((dist z y) ^ (-β)) * (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤
        ENNReal.ofReal (r ^ (-β) * ((2 : ℝ) ^ (-β)) ^ n) * ENNReal.ofReal P.C_D := by
    rw [← outer_power hr β n]
    apply P.weighted_annulus hz (by positivity) ((min_le_right _ _).trans hσρ)
      ((min_le_left _ _).trans (by rw [pow_succ]; ring_nf; rfl))
    intro y hy _
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < (2 : ℝ) ^ n * r) hy (by linarith))
  calc
    _ ≤ ∫⁻ y in ⋃ n, A n, ENNReal.ofReal ((dist z y) ^ (-β)) * (volumeAt P.μ z y)⁻¹ ∂P.μ :=
      lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
    _ ≤ ∑' n, ∫⁻ y in A n, ENNReal.ofReal ((dist z y) ^ (-β)) * (volumeAt P.μ z y)⁻¹ ∂P.μ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (r ^ (-β) * ((2 : ℝ) ^ (-β)) ^ n) * ENNReal.ofReal P.C_D :=
      ENNReal.tsum_le_tsum hA
    _ = _ := geometric_sum (by linarith [P.one_lt_C_D]) (Real.rpow_nonneg hr.le _) hβ

end RothschildStein.H2
