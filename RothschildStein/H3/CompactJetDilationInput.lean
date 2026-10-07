-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactGaugeHolderInput
public import RothschildStein.H3.CompactIntrinsicJetDilation
public import RothschildStein.H3.CompactDilationSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3

/-- Gauge Hölder bounds transport through actual group
dilation with the exact weighted scale factor (BB p. 380). -/
theorem gauge_holder_dilate {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) {R : ℝ} (hR : 0 < R)
    (degree α A : ℝ) (f : (Fin N → ℝ) → ℝ)
    (hh : ∀ x y, |f x - f y| ≤ A * G2.gaugeDistance G ν x y ^ α) :
    ∀ x y, |R ^ degree * f (G.dilate R x) - R ^ degree * f (G.dilate R y)| ≤
      (R ^ degree * A * R ^ α) * G2.gaugeDistance G ν x y ^ α := by
  intro x y
  have hp : 0 ≤ R ^ degree := (Real.rpow_pos_of_pos hR degree).le
  calc
    _ = R ^ degree * |f (G.dilate R x) - f (G.dilate R y)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hp]
    _ ≤ R ^ degree * (A * G2.gaugeDistance G ν (G.dilate R x) (G.dilate R y) ^ α) :=
      mul_le_mul_of_nonneg_left (hh _ _) hp
    _ = _ := by
      have hn : 0 ≤ G2.gaugeDistance G ν x y := ν.gauge.2.1 _
      rw [G2.gaugeDistance_dilate G ν.gauge R hR, Real.mul_rpow hR.le hn]
      ring

end RothschildStein.H3
