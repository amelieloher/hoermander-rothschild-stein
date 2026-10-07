-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependencePicard

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter Function ODE MeasureTheory
open scoped Topology NNReal

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard iterates have the factorial contraction bound on
an arbitrary bounded time interval. This avoids shrinking the time domain
at successive derivative orders (BB Proposition 1.2, p. 3). -/
theorem linearPicard_iterate_apply_dist_le
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) {K : ℝ≥0}
    (hb : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K) (w₀ : E)
    (α β : C(Icc (-T) T, E)) (n : ℕ) (t : Icc (-T) T) :
    dist ((linearPicard hT A hc w₀)^[n] α t) ((linearPicard hT A hc w₀)^[n] β t) ≤
      ((K : ℝ) * |t.1|) ^ n / n.factorial * dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := α) (g := β) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, linearPicard_apply,
      linearPicard_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (linearPicard_integrable hT A hc _ t)
        (linearPicard_integrable hT A hc _ t)]
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t.1,
          (K : ℝ) ^ (n + 1) * |s| ^ n / n.factorial * dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hs' : s ∈ Icc (-T) T :=
          (uIcc_subset_Icc (by constructor <;> linarith) t.property) (uIoc_subset_uIcc hs)
        rw [← dist_eq_norm, extendedCurve_apply _ _ hs', extendedCurve_apply _ _ hs']
        calc
          _ ≤ (K : ℝ) * dist ((linearPicard hT A hc w₀)^[n] α ⟨s, hs'⟩)
              ((linearPicard hT A hc w₀)^[n] β ⟨s, hs'⟩) :=
            ((A s).lipschitzWith_of_opNorm_le (hb s hs')).dist_le_mul _ _
          _ ≤ (K : ℝ) ^ (n + 1) * |s| ^ n / n.factorial * dist α β := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [← mul_pow] using hn ⟨s, hs'⟩
      _ ≤ ((K : ℝ) * |t.1|) ^ (n + 1) / (n + 1).factorial * dist α β := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq]
        have hi := integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := t.1) n
        simp only [sub_zero] at hi
        rw [hi]
        simp only [abs_div, abs_pow, abs_abs, abs_dist, NNReal.abs_eq, Nat.abs_cast,
          ← Nat.cast_succ]
        rw [← mul_div_assoc, div_div, ← mul_pow, Nat.factorial_succ, Nat.cast_mul]


/-- A sufficiently high Picard iterate is a contraction on the
whole Banach space of continuous curves (BB Proposition 1.2, p. 3). -/
theorem linearPicard_exists_contracting_iterate
    {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) {K : ℝ≥0}
    (hb : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ K) (w₀ : E) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C ((linearPicard hT A hc w₀)^[n]) := by
  obtain ⟨n, hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * T)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : 0 ≤ ((K : ℝ) * T) ^ n / n.factorial := by positivity
  let C : ℝ≥0 := ⟨((K : ℝ) * T) ^ n / n.factorial, hnonneg⟩
  refine ⟨n, C, hn, LipschitzWith.of_dist_le_mul ?_⟩
  intro α β
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply (linearPicard_iterate_apply_dist_le hT A hc hb w₀ α β n t).trans
  have ht : |t.1| ≤ T := abs_le.mpr t.property
  change ((K : ℝ) * |t.1|) ^ n / n.factorial * dist α β ≤
    ((K : ℝ) * T) ^ n / n.factorial * dist α β
  gcongr

end RothschildStein.G1
