-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialKernelCutoff
public import RothschildStein.H3.ControlMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- A symmetric homogeneous norm with triangle constant one
has its radial difference bounded by the actual gauge distance. -/
theorem homogeneousNorm_sub_le_gaugeDistance (ν : HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (x y : Fin N → ℝ) :
    |ν x - ν y| ≤ gaugeDistance G ν x y := by
  have hx := gaugeDistance_triangle G ν x 0 y
  have hy := gaugeDistance_triangle G ν y 0 x
  have hsymd := gaugeDistance_symmetric G ν hsym x y
  rw [hsymd] at hy
  have hz (z : Fin N → ℝ) : gaugeDistance G ν z 0 = ν z := by
    simp only [gaugeDistance, G2.inv_zero, G2.zero_mul]
  rw [h1, one_mul, hz x, hz y] at hx
  rw [h1, one_mul, hz y, hz x] at hy
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The actual group radial cutoff is measurable, compactly
supported inside the closed radius-3r ball, and has Lipschitz constant 1/r. -/
theorem radialKernelCutoff_properties (ν : HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {r : ℝ} (hr : 0 < r) :
    let χ := fun x : Fin N → ℝ => radialKernelCutoffProfile r (ν x)
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, ν x ≤ 2 * r → χ x = 1) ∧
      (∀ x, 3 * r ≤ ν x → χ x = 0) ∧
      Continuous χ ∧ HasCompactSupport χ ∧
      (∀ x y, |χ x - χ y| ≤ gaugeDistance G ν x y / r) := by
  dsimp only
  refine ⟨fun x => radialKernelCutoffProfile_range r (ν x),
    fun x hx => radialKernelCutoffProfile_eq_one hr hx,
    fun x hx => radialKernelCutoffProfile_eq_zero hr hx,
    (radialKernelCutoffProfile_continuous r).comp ν.gauge.1, ?_, ?_⟩
  · have hs : tsupport (fun x : Fin N → ℝ => radialKernelCutoffProfile r (ν x)) ⊆
        {x | ν x ≤ 3 * r} := by
      apply closure_minimal _ (isClosed_le ν.gauge.1 continuous_const)
      intro x hx
      exact le_of_not_gt (fun he => hx (radialKernelCutoffProfile_eq_zero hr he.le))
    exact (isCompact_gauge_le ν.gauge (3 * r)).of_isClosed_subset isClosed_closure hs
  · intro x y
    exact (radialKernelCutoffProfile_sub_le hr (ν x) (ν y)).trans
      (div_le_div_of_nonneg_right (homogeneousNorm_sub_le_gaugeDistance ν h1 hsym x y) hr.le)

end RothschildStein.H3
