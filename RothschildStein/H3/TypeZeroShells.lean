-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZero
public import RothschildStein.H3.TruncatedShells
public import RothschildStein.H1.ShellRadialWeight
public import RothschildStein.H1.OpenShellBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The defining type-zero mean supplies cancellation on every positive
shell through the logarithmic shell formula. -/
theorem TypeZero.vanishingShellIntegrals {ν : G2.HomogeneousNorm G}
    {f : (Fin N → ℝ) → ℝ} (hf : TypeZero G ν f) :
    H1.HasVanishingShellIntegrals ν f := by
  apply (H1.vanishingShellIntegrals_iff_mean_zero G ν.gauge
    hf.smooth.continuousOn hf.homogeneous).mpr
  exact hf.mean_zero

/-- Continuous radial weights preserve the type-zero shell
cancellation. The strict-shell convention is transferred through null boundaries. -/
theorem TypeZero.radial_shell_zero {ν : G2.HomogeneousNorm G}
    {f : (Fin N → ℝ) → ℝ} (hf : TypeZero G ν f)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {Φ : ℝ → ℝ} (hΦ : ContinuousOn Φ (Icc a b)) :
    (∫ x in {x | a < ν x ∧ ν x < b}, f x * Φ (ν x)) = 0 := by
  rw [H1.integral_openGaugeShell_eq_closed G ν.gauge ha (ha.trans hab)]
  exact H1.integral_gaugeShell_radialWeight_zero G ν.gauge
    hf.smooth.continuousOn (hf.vanishingShellIntegrals G) ha hab hΦ

/-- The actual truncated type-zero kernel has exact strong
shell cancellation for arbitrary positive radii. -/
theorem TypeZero.truncatedKernel_shell_zero {ν : G2.HomogeneousNorm G}
    {f : (Fin N → ℝ) → ℝ} (hf : TypeZero G ν f)
    (x : Fin N → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ y in {y | a < G2.gaugeDistance G ν x y ∧ G2.gaugeDistance G ν x y < b},
      truncatedKernel G ν f x y) = 0 := by
  apply truncatedKernel_shell_zero_of_radial_shells G ν f ?_ x ha hab
  intro a b ha hab Φ hΦ
  exact hf.radial_shell_zero G ha hab hΦ

end RothschildStein.H3
