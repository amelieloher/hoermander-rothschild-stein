-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.ComplexFiniteOrder
public import RothschildStein.Distribution.CutoffSchwartzBound
public import RothschildStein.Distribution.LocalizedTempered
public import RothschildStein.Distribution.SchwartzPostcompBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace SchwartzMap
open scoped BigOperators
namespace RothschildStein.Distribution
variable {N : ℕ}

/-- cutoff localization gives an actual finite
unweighted Schwartz bound for a complex-valued real-test distribution. -/
theorem localizedRealSchwartz_finiteOrder (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞)) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap (Fin N → ℝ) ℝ,
      ‖T (S.schwartzCutoffTestCLM U χ φ)‖ ≤
        C * ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℝ 0 j φ := by
  let K : Compacts (Fin N → ℝ) := ⟨tsupport χ, χ.hasCompactSupport⟩
  let χK : ContDiffMapSupportedIn (Fin N → ℝ) ℝ (⊤ : ℕ∞) K :=
    .of_support_subset χ.contDiff subset_closure
  obtain ⟨r, C, hC, h⟩ := distribution_finite_order_complex U T K χ.tsupport_subset
  let M := ContDiffMapSupportedIn.supSeminorm ℝ (Fin N → ℝ) ℝ (⊤ : ℕ∞) K r χK
  have hM : 0 ≤ M := apply_nonneg _ _
  refine ⟨r, C * (2 ^ r * M), by positivity, fun φ => ?_⟩
  have hb : ContDiffMapSupportedIn.supSeminorm ℝ (Fin N → ℝ) ℝ (⊤ : ℕ∞) K r
      (S.schwartzCutoffFixedCLM U χ φ) ≤
      2 ^ r * M * ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℝ 0 j φ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    exact cutoffSchwartz_seminorm_le U χ r i (Finset.mem_Iic.mp hi) φ
  exact (h (S.schwartzCutoffFixedCLM U χ φ)).trans
    ((mul_le_mul_of_nonneg_left hb hC).trans_eq (by ring))

/-- the localized tempered distribution itself has
finite unweighted derivative order, including complex test inputs. -/
theorem localizedTempered_finiteSchwartzOrder (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞)) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SchwartzMap (Fin N → ℝ) ℂ,
      ‖localizedTempered U χ T φ‖ ≤
        C * ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℂ 0 j φ := by
  obtain ⟨r, C, hC, h⟩ := localizedRealSchwartz_finiteOrder U χ T
  refine ⟨r, C * (‖Complex.reCLM‖ + ‖Complex.imCLM‖), by positivity, fun φ => ?_⟩
  have hp (L : ℂ →L[ℝ] ℝ) :
      (∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℝ 0 j
        (SchwartzMap.postcompCLM L φ)) ≤
      ‖L‖ * ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℂ 0 j φ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have he : SchwartzMap.seminorm ℝ 0 j φ = SchwartzMap.seminorm ℂ 0 j φ := by
      rw [SchwartzMap.seminorm_apply, SchwartzMap.seminorm_apply]
    simpa only [he] using schwartzSeminorm_postcomp_le L j φ
  rw [localizedTempered_apply]
  calc
    _ ≤ ‖T (S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM Complex.reCLM φ))‖ +
        ‖T (S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM Complex.imCLM φ))‖ := by
      simpa only [norm_mul, Complex.norm_I, one_mul] using norm_add_le
        (T (S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM Complex.reCLM φ)))
        (Complex.I * T (S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM Complex.imCLM φ)))
    _ ≤ C * (‖Complex.reCLM‖ * ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℂ 0 j φ) +
        C * (‖Complex.imCLM‖ * ∑ j ∈ Finset.range (r + 1), SchwartzMap.seminorm ℂ 0 j φ) :=
      add_le_add ((h _).trans (mul_le_mul_of_nonneg_left (hp Complex.reCLM) hC))
        ((h _).trans (mul_le_mul_of_nonneg_left (hp Complex.imCLM) hC))
    _ = _ := by ring

end RothschildStein.Distribution
