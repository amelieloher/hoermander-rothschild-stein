-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellDefs
public import RothschildStein.G2.DilationMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A continuous homogeneous kernel is bounded by the
matching gauge power, by normalization on the compact unit shell
(BB Proposition 6.29, pp. 276–278). -/
theorem exists_homogeneousKernel_gauge_bound
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hc : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ) {β : ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ≠ 0 → ‖f x‖ ≤ C * (ν x) ^ β := by
  have hK := isCompact_gaugeShell hν 1 1
  have hfc : ContinuousOn f (gaugeShell ν 1 1) :=
    hc.mono (gaugeShell_subset_punctured hν (by norm_num))
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hfc).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hp : 0 < ν x := lt_of_le_of_ne (hν.2.1 x) (Ne.symm fun h => hx ((hν.2.2.1 x).mp h))
  let z := G.dilate (ν x)⁻¹ x
  have hzν : ν z = 1 := by
    change ν (G.dilate (ν x)⁻¹ x) = 1
    rw [hν.2.2.2 _ (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  have hν0 : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have hz : z ≠ 0 := by intro he; rw [he, hν0] at hzν; norm_num at hzν
  have hzK : z ∈ gaugeShell ν 1 1 := by change 1 ≤ ν z ∧ ν z ≤ 1; rw [hzν]; exact ⟨le_rfl, le_rfl⟩
  have hb : ‖f z‖ ≤ max C 0 := (hC _ ⟨z, hzK, rfl⟩).trans (le_max_left _ _)
  have hs := hf (ν x) hp z hz
  change f (G.dilate (ν x) (G.dilate (ν x)⁻¹ x)) = (ν x) ^ β * f z at hs
  rw [G2.dilate_dilate, mul_inv_cancel₀ hp.ne', G2.dilate_one] at hs
  rw [hs, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hp.le _)).trans_eq (mul_comm _ _)

end RothschildStein.H1
