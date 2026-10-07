-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellGeometry
public import RothschildStein.H1.ShellScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The shell primitive in logarithmic radius (BB (6.39)). -/
def logShellPrimitive (ν f : (Fin N → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x in gaugeShell ν 1 (Real.exp t), f x

/-- The primitive is zero at logarithmic radius zero, because
the unit level has zero volume (BB p. 274). -/
theorem logShellPrimitive_zero {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) :
    logShellPrimitive ν f 0 = 0 := by
  have he : gaugeShell ν 1 1 = {x : Fin N → ℝ | ν x = 1} := by
    ext x
    exact ⟨fun hx => le_antisymm hx.2 hx.1, fun hx => ⟨hx.ge, hx.le⟩⟩
  rw [logShellPrimitive, Real.exp_zero, he,
    Measure.restrict_eq_zero.mpr (volume_gauge_level G hν (by norm_num : (0 : ℝ) < 1)),
    integral_zero_measure]

/-- Critical homogeneity makes the logarithmic primitive
additive on nonnegative radii (BB (6.39), p. 274). -/
theorem logShellPrimitive_add_nonneg {ν f : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hc : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    logShellPrimitive ν f (a + b) = logShellPrimitive ν f a + logShellPrimitive ν f b := by
  have h1 : (1 : ℝ) ≤ Real.exp a := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ha
  have h2 : Real.exp a ≤ Real.exp (a + b) := Real.exp_le_exp.mpr (by linarith)
  have he := integral_gaugeShell_add G hν hc (by norm_num : (0 : ℝ) < 1) h1 h2
  have hs := integral_gaugeShell_scale G hν hf (r := 1) (R := Real.exp b)
    (by norm_num) (Real.exp_pos a)
  rw [mul_one, ← Real.exp_add] at hs
  change (∫ x in gaugeShell ν 1 (Real.exp (a + b)), f x) = _
  rw [he, hs]
  rfl

end RothschildStein.H1
