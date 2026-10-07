-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SmoothRepresentative.Uniqueness
public import Hormander.A.SobolevScale

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform

namespace Hormander.A

/-- Auxiliary: the Bessel weight `(1 + ‖ξ‖²)^(-r/2)` is square integrable when `N < 2r`. -/
theorem memLp_bessel_weight {N : ℕ} {r : ℝ} (hr : (N : ℝ) < 2 * r) :
    MemLp (fun x : Carrier N ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)) 2 (volume : Measure (Carrier N)) := by
  have htemp : (fun x : Carrier N ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)).HasTemperateGrowth := by
    fun_prop
  have hmeas : AEStronglyMeasurable (fun x : Carrier N ↦ (1 + ‖x‖ ^ 2) ^ (-r / 2)) :=
    htemp.1.continuous.aestronglyMeasurable
  have hfin : Module.finrank ℝ (Carrier N) < 2 * r := by simpa using hr
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hmeas]
  suffices h : ∫⁻ a : Carrier N, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-r)‖ < ⊤ by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hfin).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

/-- Auxiliary: from `T ∈ H^s` with `N < 2 s`, the Fourier transform of `T` is the `L¹` function
`w · u` where `w = (1+‖ξ‖²)^(-s/2)` and `u ∈ L²` is the weighted Fourier representative. -/
theorem exists_fourier_weight_mul {N : ℕ} {s : ℝ} (hs : (N : ℝ) < 2 * s)
    {T : 𝓢'(Carrier N, ℂ)} (hT : MemSobolev s 2 T) :
    ∃ (u : Lp ℂ 2 (volume : Measure (Carrier N))) (v : Lp ℂ 1 (volume : Measure (Carrier N))),
      𝓕 T = (v : 𝓢'(Carrier N, ℂ)) ∧
        (∀ᵐ ξ, v ξ = Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-s / 2)) * u ξ) := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hT
  have hw := memLp_bessel_weight (N := N) hs
  have hw' : MemLp (fun x : Carrier N ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 :=
    hw.ofReal
  have htemp : (fun x : Carrier N ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)).HasTemperateGrowth := by
    fun_prop
  refine ⟨u, hw'.toLp _ • u, ?_, ?_⟩
  · rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq htemp hw' u]
    rw [← hu, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert! (smulLeftCLM_const 1 (𝓕 T)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · filter_upwards [Lp.coeFn_lpSMul (r := 1) (hw'.toLp _) u, hw'.coeFn_toLp] with x h1 h2
    simp [h1, h2]

/-- Weighted Cauchy–Schwarz: if `T ∈ H^s` with `s > n + N/2` and
`v` is an `L¹` representative of `𝓕 T`, then `‖ξ‖ⁿ ‖v ξ‖` is integrable. -/
theorem integrable_norm_pow_mul_fourier {N : ℕ} {s : ℝ} {n : ℕ}
    (hs : (n : ℝ) + N / 2 < s) {T : 𝓢'(Carrier N, ℂ)} (hT : MemSobolev s 2 T)
    (v : Lp ℂ 1 (volume : Measure (Carrier N))) (hv : 𝓕 T = (v : 𝓢'(Carrier N, ℂ))) :
    Integrable (fun ξ : Carrier N ↦ ‖ξ‖ ^ n * ‖v ξ‖) := by
  have hs' : (N : ℝ) < 2 * s := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨u, v', hv', hae⟩ := exists_fourier_weight_mul hs' hT
  have hvv : v' = v := lp_eq_of_toTemperedDistribution_eq (hv'.symm.trans hv)
  subst hvv
  have hw := memLp_bessel_weight (N := N) (r := s - n) (by linarith)
  have hint : Integrable ((fun x : Carrier N ↦ (1 + ‖x‖ ^ 2) ^ (-(s - n) / 2)) *
      fun x ↦ ‖u x‖) volume :=
    MemLp.integrable_mul (p := 2) (q := 2) hw (Lp.memLp u).norm
  refine hint.mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun ξ : Carrier N ↦ ‖ξ‖ ^ n).aestronglyMeasurable).mul
      (Lp.memLp v').aestronglyMeasurable.norm
  · filter_upwards [hae] with ξ hξ
    have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    have h1 : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) := by
      have : ‖ξ‖ ^ n = (‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        push_cast
        ring
      rw [this]
      exact Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg ξ]) (by positivity)
    have h2 : ‖v' ξ‖ = (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * ‖u ξ‖ := by
      rw [hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), h2]
    simp only [Pi.mul_apply]
    calc ‖ξ‖ ^ n * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2) * ‖u ξ‖)
        ≤ (1 + ‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) * ((1 + ‖ξ‖ ^ 2) ^ (-s / 2) * ‖u ξ‖) := by
          gcongr
      _ = (1 + ‖ξ‖ ^ 2) ^ (-(s - n) / 2) * ‖u ξ‖ := by
          rw [← mul_assoc, ← Real.rpow_add hpos]
          congr 2
          ring

end Hormander.A
