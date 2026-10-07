-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.SchwartzDerivativeBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped FourierTransform
namespace RothschildStein.Distribution

/-- lowering the Schwartz Sobolev order does not
increase the source Fourier norm. -/
theorem schwartzSobolev_norm_mono {N : ℕ} {s t : ℝ} (hst : s ≤ t)
    (φ : 𝓢(Hormander.A.Carrier N, ℂ)) :
    ‖Hormander.A.schwartzToSobolev s φ‖ ≤ ‖Hormander.A.schwartzToSobolev t φ‖ := by
  rw [← weightedFourier_norm s φ, ← weightedFourier_norm t φ]
  let ψs := SchwartzMap.smulLeftCLM ℂ (Hormander.A.besselSymbol s) (𝓕 φ)
  let ψt := SchwartzMap.smulLeftCLM ℂ (Hormander.A.besselSymbol t) (𝓕 φ)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ψs.coeFn_toLp 2 volume, ψt.coeFn_toLp 2 volume] with ξ hsξ htξ
  rw [hsξ, htξ]
  change ‖ψs ξ‖ ≤ ‖ψt ξ‖
  rw [show ψs ξ = Hormander.A.besselSymbol s ξ * 𝓕 φ ξ from
    SchwartzMap.smulLeftCLM_apply_apply (Hormander.A.besselSymbol_hasTemperateGrowth s) _ ξ,
    show ψt ξ = Hormander.A.besselSymbol t ξ * 𝓕 φ ξ from
    SchwartzMap.smulLeftCLM_apply_apply (Hormander.A.besselSymbol_hasTemperateGrowth t) _ ξ,
    norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simp only [Hormander.A.besselSymbol, Complex.norm_real]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖]) (by linarith)

end RothschildStein.Distribution
