-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Scale.Riesz

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap TemperedDistribution
open scoped FourierTransform BesselPotentialSpace
namespace RothschildStein.Distribution

/-- the Fourier-weighted Schwartz norm is exactly
the bundled Sobolev norm, with the source Japanese-bracket symbol. -/
theorem weightedFourier_norm {N : ℕ} (s : ℝ) (φ : 𝓢(Hormander.A.Carrier N, ℂ)) :
    ‖(SchwartzMap.smulLeftCLM ℂ (Hormander.A.besselSymbol s) (𝓕 φ)).toLp 2‖ =
      ‖Hormander.A.schwartzToSobolev s φ‖ := by
  rw [← Hormander.A.fourier_Lambda, ← SchwartzMap.toLp_fourier_eq]
  rw [Lp.norm_fourier_eq]
  exact Hormander.A.schwartzSobolevNorm_eq_schwartzToSobolev_norm s φ

/-- a bound by the exact source Hᴹ Fourier norm
places the actual tempered distribution in H⁻ᴹ. -/
theorem memSobolev_neg_of_schwartz_dualityBound {N : ℕ} (M : ℝ) (_hM : 0 ≤ M)
    (v : 𝓢'(Hormander.A.Carrier N, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(Hormander.A.Carrier N, ℂ), ‖v φ‖ ≤
      C * ‖(SchwartzMap.smulLeftCLM ℂ (Hormander.A.besselSymbol M) (𝓕 φ)).toLp 2‖) :
    TemperedDistribution.MemSobolev (-M) 2 v := by
  have hb (φ : 𝓢(Hormander.A.Carrier N, ℂ)) :
      ‖v φ‖ ≤ C * ‖Hormander.A.schwartzToSobolev M φ‖ := by
    simpa only [weightedFourier_norm] using h φ
  obtain ⟨w, hw, _⟩ := Hormander.A.riesz_converse M v hC hb
  rw [← hw]
  exact BesselPotentialSpace.memSobolev_toDistr w

end RothschildStein.Distribution
