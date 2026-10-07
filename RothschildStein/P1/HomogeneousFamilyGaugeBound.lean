-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.H1.HomogeneousKernelBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {N : ℕ}

/-- Homogeneous model families have size bounds
for any homogeneous gauge, uniformly over a compact endpoint patch. -/
theorem exists_homogeneousFamily_gauge_bound
    (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hc : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0}) {β : ℝ}
    (hhom : ∀ ξ η, ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ β * Ψ ξ η u)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ ∈ K, ∀ η ∈ K, ∀ u, u ≠ 0 →
      ‖Ψ ξ η u‖ ≤ M * ν u ^ β := by
  have hS := hK.prod (hK.prod (H1.isCompact_gaugeShell hν 1 1))
  have hsub : K ×ˢ (K ×ˢ H1.gaugeShell ν 1 1) ⊆
      {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} := by
    intro z hz
    exact H1.gaugeShell_subset_punctured hν (by norm_num : (0 : ℝ) < 1) hz.2.2
  obtain ⟨B, hb⟩ := hS.exists_bound_of_continuousOn (hc.mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro ξ hξ η hη u hu
  have hp : 0 < ν u := lt_of_le_of_ne (hν.2.1 u)
    (Ne.symm (fun hz => hu ((hν.2.2.1 u).mp hz)))
  let z := G.dilate (ν u)⁻¹ u
  have hzν : ν z = 1 := by
    change ν (G.dilate (ν u)⁻¹ u) = 1
    rw [hν.2.2.2 _ (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  have hz : z ≠ 0 := by
    intro h0
    have hn0 : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
    rw [h0, hn0] at hzν
    norm_num at hzν
  have hzS : z ∈ H1.gaugeShell ν 1 1 := by
    change 1 ≤ ν z ∧ ν z ≤ 1
    rw [hzν]
    exact ⟨le_rfl, le_rfl⟩
  have hB : ‖Ψ ξ η z‖ ≤ max B 0 :=
    (hb (ξ, η, z) ⟨hξ, hη, hzS⟩).trans (le_max_left _ _)
  have he := hhom ξ η (ν u) hp z hz
  change Ψ ξ η (G.dilate (ν u) (G.dilate (ν u)⁻¹ u)) = ν u ^ β * Ψ ξ η z at he
  rw [G2.dilate_dilate, mul_inv_cancel₀ hp.ne', G2.dilate_one] at he
  rw [he, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  exact (mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hp.le _)).trans_eq (mul_comm _ _)

end RothschildStein.P1
