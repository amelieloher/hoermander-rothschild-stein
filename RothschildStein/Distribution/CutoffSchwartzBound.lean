-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SchwartzLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace SchwartzMap
open scoped BigOperators
namespace RothschildStein.Distribution
variable {N : ℕ}

/-- localization has an unweighted finite-order
bound, obtained by the finite Leibniz sum on the fixed support. -/
theorem cutoffSchwartz_seminorm_le (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (r i : ℕ) (hi : i ≤ r)
    (φ : SchwartzMap (Fin N → ℝ) ℝ) :
    ContDiffMapSupportedIn.seminorm ℝ (Fin N → ℝ) ℝ (⊤ : ℕ∞)
      (⟨tsupport χ, χ.hasCompactSupport⟩ : Compacts (Fin N → ℝ)) i
      (S.schwartzCutoffFixedCLM U χ φ) ≤
    2 ^ r * ContDiffMapSupportedIn.supSeminorm ℝ (Fin N → ℝ) ℝ (⊤ : ℕ∞)
      (⟨tsupport χ, χ.hasCompactSupport⟩ : Compacts (Fin N → ℝ)) r
      (.of_support_subset χ.contDiff subset_closure) *
      ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℝ 0 j φ := by
  let K : Compacts (Fin N → ℝ) := ⟨tsupport χ, χ.hasCompactSupport⟩
  let χK : ContDiffMapSupportedIn (Fin N → ℝ) ℝ (⊤ : ℕ∞) K :=
    .of_support_subset χ.contDiff subset_closure
  let M := ContDiffMapSupportedIn.supSeminorm ℝ (Fin N → ℝ) ℝ (⊤ : ℕ∞) K r χK
  let B := ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℝ 0 j φ
  have hM : 0 ≤ M := apply_nonneg _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  apply (ContDiffMapSupportedIn.seminorm_le_iff ℝ (by positivity) i _).mpr
  intro _ x _
  have hf : ∀ j ≤ i, ‖iteratedFDeriv ℝ j φ x‖ ≤ B := by
    intro j hj
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ j x).trans
      (Finset.single_le_sum (fun _ _ => apply_nonneg _ _)
        (Finset.mem_range_succ_iff.mpr (hj.trans hi)))
  have hχ : ∀ j ≤ i, ‖iteratedFDeriv ℝ j χ x‖ ≤ M := by
    intro j hj
    exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ
      (f := χK) (by simp)).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr (hj.trans hi)))
  change ‖iteratedFDeriv ℝ i (fun y => φ y * χ y) x‖ ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j φ x‖ * ‖iteratedFDeriv ℝ (i-j) χ x‖ :=
      norm_iteratedFDeriv_mul_le (φ.smooth (⊤ : ℕ∞)) χ.contDiff x (by simp)
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * B * M := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact hf j (Finset.mem_range_succ_iff.mp hj)
      · exact hχ (i-j) (Nat.sub_le _ _)
    _ = 2 ^ i * M * B := by
      simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    _ ≤ 2 ^ r * M * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hi) hM) hB

end RothschildStein.Distribution
