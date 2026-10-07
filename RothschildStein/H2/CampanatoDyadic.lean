-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoConstants
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Dyadic Campanato radii indexed from zero. -/
def campanatoRadius (r : ℝ) (n : ℕ) : ℝ := r * (1 / 2 : ℝ) ^ n

/-- Basic radius identities used in BB Lemma 7.40. -/
theorem campanatoRadius_facts {r : ℝ} (hr : 0 < r) (n : ℕ) :
    0 < campanatoRadius r n ∧ campanatoRadius r n ≤ r ∧
      campanatoRadius r (n + 1) = campanatoRadius r n / 2 := by
  refine ⟨mul_pos hr (pow_pos (by norm_num) _), ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hr.le).trans_eq (mul_one r)
  · simp only [campanatoRadius, pow_succ]; ring

/-- Dyadic radius powers form a geometric series of ratio 2^{-α}. -/
theorem campanatoRadius_rpow {r α : ℝ} (hr : 0 < r) (n : ℕ) :
    (campanatoRadius r n) ^ α = r ^ α * ((1 / 2 : ℝ) ^ α) ^ n := by
  rw [campanatoRadius, Real.mul_rpow hr.le (by positivity),
    ← Real.rpow_natCast_mul (by norm_num), mul_comm (n : ℝ) α,
    Real.rpow_mul_natCast (by norm_num)]

/-- Every controlled radius gives a convergent sequence of minimisers,
with the explicit geometric tail (BB Lemmas 7.40–7.42, pp. 328–329). -/
theorem campanato_dyadic_limit (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    ∃ L : ℝ,
      Tendsto (fun n => campanatoConstant P u x (campanatoRadius r n)) atTop (𝓝 L) ∧
      ∀ n : ℕ, |campanatoConstant P u x (campanatoRadius r n) - L| ≤
        ((P.C_D + 1) * r ^ α * (campanatoSeminorm α P u).toReal) *
          ((1 / 2 : ℝ) ^ α) ^ n / (1 - (1 / 2 : ℝ) ^ α) := by
  let q := (1 / 2 : ℝ) ^ α
  let C := (P.C_D + 1) * r ^ α * (campanatoSeminorm α P u).toReal
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hstep (n : ℕ) :
      dist (campanatoConstant P u x (campanatoRadius r n))
        (campanatoConstant P u x (campanatoRadius r (n + 1))) ≤ C * q ^ n := by
    have hf := campanatoRadius_facts hr n
    rw [hf.2.2, Real.dist_eq]
    have hb := campanatoConstant_halving P hα.le hu hx hf.1 (hf.2.1.trans hrρ)
    rw [campanatoRadius_rpow hr n] at hb
    dsimp [C, q]; nlinarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq hstep)
  refine ⟨L, hL, fun n => ?_⟩
  simpa only [Real.dist_eq] using dist_le_of_le_geometric_of_tendsto q C hq hstep hL n
end RothschildStein.H2
