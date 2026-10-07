-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Dilation preserves every critical-degree shell integral
(BB Proposition 6.26(1), (6.37), p. 274). -/
theorem integral_gaugeShell_scale
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x)
    {r R c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (∫ x in gaugeShell ν (c * r) (c * R), f x) = ∫ x in gaugeShell ν r R, f x := by
  have hs (x : Fin N → ℝ) : G.dilate c x ∈ gaugeShell ν (c * r) (c * R) ↔
      x ∈ gaugeShell ν r R := by
    change c * r ≤ ν (G.dilate c x) ∧ ν (G.dilate c x) ≤ c * R ↔ r ≤ ν x ∧ ν x ≤ R
    rw [hν.2.2.2 _ hc, mul_le_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hc]
  have he : (fun x => (gaugeShell ν (c * r) (c * R)).indicator f (G.dilate c x)) =
      fun x => (c ^ G.homogeneousDimension)⁻¹ * (gaugeShell ν r R).indicator f x := by
    funext x
    by_cases hx : x ∈ gaugeShell ν r R
    · rw [indicator_of_mem ((hs x).mpr hx), indicator_of_mem hx,
        hf c hc x (gaugeShell_subset_punctured hν hr hx), Real.rpow_neg hc.le, Real.rpow_natCast]
    · rw [indicator_of_notMem (fun h => hx ((hs x).mp h)), indicator_of_notMem hx, mul_zero]
  have hi := G2.integral_dilate G hc ((gaugeShell ν (c * r) (c * R)).indicator f)
  rw [he, integral_const_mul] at hi
  change (c ^ G.homogeneousDimension)⁻¹ * (∫ x, (gaugeShell ν r R).indicator f x) =
    (c ^ G.homogeneousDimension)⁻¹ * (∫ x, (gaugeShell ν (c * r) (c * R)).indicator f x) at hi
  have hn : (c ^ G.homogeneousDimension)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc.ne')
  have hh := mul_left_cancel₀ hn hi
  rw [integral_indicator (measurableSet_gaugeShell hν r R),
    integral_indicator (measurableSet_gaugeShell hν (c * r) (c * R))] at hh
  exact hh.symm

end RothschildStein.H1
