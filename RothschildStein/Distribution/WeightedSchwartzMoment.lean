-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.SobolevDuality
public import Hormander.A.SmoothRepresentative.WeightedL1
public import Hormander.A.SmoothRepresentative.InverseIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped FourierTransform
namespace RothschildStein.Distribution

/-- scalar Cauchy–Schwarz in the actual L²
spaces, retaining the norm of the given weight. -/
theorem integral_mul_le_toLp_norms {N : ℕ}
    {f g : Hormander.A.Carrier N → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ ξ, f ξ * g ξ) ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have he : (∫ ξ, f ξ * g ξ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ξ hξf hξg
    simp only [hξf, hξg, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [he]
  exact real_inner_le_norm _ _

/-- the weighted Fourier Cauchy–Schwarz estimate
for every nonnegative integer moment below the Sobolev order. -/
theorem integral_fourier_moment_le {N : ℕ} (n : ℕ) (s : ℝ)
    (hs : (N : ℝ) < 2 * s) (φ : 𝓢(Hormander.A.Carrier N, ℂ)) :
    (∫ ξ, ‖ξ‖ ^ n * ‖𝓕 φ ξ‖) ≤
      ‖(Hormander.A.memLp_bessel_weight hs).toLp
        (fun ξ : Hormander.A.Carrier N => (1 + ‖ξ‖ ^ 2) ^ (-s / 2))‖ *
      ‖Hormander.A.schwartzToSobolev ((n : ℝ) + s) φ‖ := by
  let w : Hormander.A.Carrier N → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2) ^ (-s / 2)
  let ψ := SchwartzMap.smulLeftCLM ℂ (Hormander.A.besselSymbol ((n : ℝ) + s)) (𝓕 φ)
  have hw : MemLp w 2 volume := Hormander.A.memLp_bessel_weight hs
  have hu : MemLp (fun ξ => ‖ψ ξ‖) 2 volume := (ψ.memLp 2 volume).norm
  have hi : Integrable (fun ξ => w ξ * ‖ψ ξ‖) volume := hw.integrable_mul hu
  have hb (ξ : Hormander.A.Carrier N) : ‖ξ‖ ^ n * ‖𝓕 φ ξ‖ ≤ w ξ * ‖ψ ξ‖ := by
    have hp : 0 < (1 + ‖ξ‖ ^ 2 : ℝ) := by positivity
    have hpow : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) := by
      have he : ‖ξ‖ ^ n = (‖ξ‖ ^ 2) ^ ((n : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        push_cast
        ring
      rw [he]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    change _ ≤ (1 + ‖ξ‖ ^ 2) ^ (-s / 2) * ‖ψ ξ‖
    rw [show ψ ξ = Hormander.A.besselSymbol ((n : ℝ) + s) ξ * 𝓕 φ ξ from
      SchwartzMap.smulLeftCLM_apply_apply (Hormander.A.besselSymbol_hasTemperateGrowth _) _ ξ]
    rw [norm_mul, Hormander.A.besselSymbol, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
    rw [← mul_assoc, ← Real.rpow_add hp]
    have he : -s / 2 + ((n : ℝ) + s) / 2 = (n : ℝ) / 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  have hnorm : ‖hu.toLp (fun ξ => ‖ψ ξ‖)‖ = ‖ψ.toLp 2‖ := by
    rw [Lp.norm_toLp, SchwartzMap.norm_toLp, eLpNorm_norm]
    exact ψ.continuous.aestronglyMeasurable
  calc
    _ ≤ ∫ ξ, w ξ * ‖ψ ξ‖ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ξ => by positivity) hi (Filter.Eventually.of_forall hb)
    _ ≤ ‖hw.toLp w‖ * ‖hu.toLp (fun ξ => ‖ψ ξ‖)‖ := integral_mul_le_toLp_norms hw hu
    _ = _ := by rw [hnorm, weightedFourier_norm]

end RothschildStein.Distribution
