-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestOperators
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import RothschildStein.S.DistributionWords
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology SchwartzMap
namespace RothschildStein.S
variable {n : ℕ}

/-- Localization sends Schwartz functions continuously to fixed
compact-support smooth functions (BB pp. 68–69). -/
def schwartzCutoffFixedCLM (U : Opens (Fin n → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) :
    SchwartzMap (Fin n → ℝ) ℝ →L[ℝ]
      ContDiffMapSupportedIn (Fin n → ℝ) ℝ (⊤ : ℕ∞)
        (⟨tsupport χ,χ.hasCompactSupport⟩ : Compacts (Fin n → ℝ)) := by
  let L : Compacts (Fin n → ℝ) := ⟨tsupport χ,χ.hasCompactSupport⟩
  let χL : ContDiffMapSupportedIn (Fin n → ℝ) ℝ (⊤ : ℕ∞) L :=
    .of_support_subset χ.contDiff subset_closure
  let A : SchwartzMap (Fin n → ℝ) ℝ →ₗ[ℝ]
      ContDiffMapSupportedIn (Fin n → ℝ) ℝ (⊤ : ℕ∞) L :=
    { toFun := fun f => ⟨fun x => f x * χ x,(f.smooth (⊤ : ℕ∞)).mul χ.contDiff,
        by intro x hx; simp [image_eq_zero_of_notMem_tsupport hx]⟩
      map_add' := by intro f g; ext x; change (f x+g x)*χ x = f x*χ x + g x*χ x; ring
      map_smul' := by intro c f; ext x; change (c*f x)*χ x = c*(f x*χ x); ring }
  refine ⟨A,?_⟩
  apply WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms ℝ _ _)
    (ContDiffMapSupportedIn.withSeminorms ..) A
  apply Seminorm.IsBounded.of_real
  intro i
  let s : Finset (ℕ × ℕ) := (Finset.Iic i).image (fun j => (0,j))
  let M := ContDiffMapSupportedIn.supSeminorm ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) L i χL
  refine ⟨s,2^i*M,fun f => ?_⟩
  apply (ContDiffMapSupportedIn.seminorm_le_iff ℝ (by positivity) i _).mpr
  intro _ x _
  let B := (s.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℝ)) f
  have hf : ∀ j ≤ i, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
    intro j hj
    apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f j x).trans
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using
      (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ (Fin n → ℝ) ℝ)
        (x := f) (i := (0,j))
        (Finset.mem_image.mpr ⟨j,Finset.mem_Iic.mpr hj,rfl⟩) :
          (schwartzSeminormFamily ℝ (Fin n → ℝ) ℝ) (0,j) f ≤ B)
  have hχ : ∀ j ≤ i, ‖iteratedFDeriv ℝ j χ x‖ ≤ M := by
    intro j hj
    exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ
      (f := χL) (by simp)).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hj))
  change ‖iteratedFDeriv ℝ i (fun y => f y * χ y) x‖ ≤ _
  calc
    _ ≤ ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) *
      ‖iteratedFDeriv ℝ j f x‖ * ‖iteratedFDeriv ℝ (i-j) χ x‖ :=
        norm_iteratedFDeriv_mul_le (f.smooth (⊤ : ℕ∞)) χ.contDiff x (by simp)
    _ ≤ ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ) * B * M := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      · exact hf j (Finset.mem_range_succ_iff.mp hj)
      · exact hχ (i-j) (Nat.sub_le _ _)
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      dsimp [B]
      ring

/-- Schwartz localization as a continuous real-linear map to tests
(BB pp. 68–69). -/
def schwartzCutoffTestCLM (U : Opens (Fin n → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) :
    SchwartzMap (Fin n → ℝ) ℝ →L[ℝ] TestFunction U ℝ (⊤ : ℕ∞) :=
  (TestFunction.ofSupportedInCLM ℝ χ.tsupport_subset).comp (schwartzCutoffFixedCLM U χ)

end RothschildStein.S
