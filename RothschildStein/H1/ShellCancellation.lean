-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellLogFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The normalized mean is zero exactly when every shell
integral vanishes (BB Remark 6.27, pp. 274–275). -/
theorem vanishingShellIntegrals_iff_mean_zero
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hc : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x) :
    HasVanishingShellIntegrals ν f ↔ homogeneousShellMean ν f = 0 := by
  constructor
  · intro he
    exact he 1 (Real.exp 1) (by norm_num)
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1))
  · intro he r R hr hrR
    rw [integral_gaugeShell_eq_mean_mul_log G hν hc hf hr hrR, he, zero_mul]

end RothschildStein.H1
