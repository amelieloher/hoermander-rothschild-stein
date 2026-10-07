-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialFirstWeight
public import RothschildStein.L1.ZeroOrderCircleField
public import RothschildStein.L1.CanonicalBasisBracketExpansion
public import RothschildStein.G3.ModelPackage
public import RothschildStein.L1.WeightedFieldBrackets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- The difference of actual and model basis commutators has the strict
combined weight when the basis remainders have their finite strict weights. -/
theorem canonical_basis_bracket_remainder_weight_of_basis_remainders
    {a s q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (hR : ∀ k, fieldJetClass (ball 0 C.radius) D.weight (1 - (D.weight k : ℝ)) q
      (fun u => C.coordinateField η k u - canonicalWordFrame D D.fields k u))
    (i j : Fin (freeDimension a s p)) :
    fieldJetClass (ball 0 C.radius) D.weight (1 - (D.weight i : ℝ) - D.weight j) q
      (fun u => VectorField.lieBracket ℝ (C.coordinateField η i) (C.coordinateField η j) u -
        VectorField.lieBracket ℝ (canonicalWordFrame D D.fields i)
          (canonicalWordFrame D D.fields j) u) := by
  let U : Opens (Fin (freeDimension a s p) → ℝ) := ⟨ball 0 C.radius,isOpen_ball⟩
  have h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ U := mem_ball_self C.radius_pos
  have hMX : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields k) U :=
    fun k => (freeModel_fields_smooth D k).contDiffOn
  have hMY := fun k => G1.wordBracket_contDiffOn U.isOpen D.fields hMX (modelBasisWord D k)
  have hY := fun k => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D k)
  by_cases hij : D.weight i + D.weight j ≤ s
  · have hs := fieldJetClass_sum U h0 D.weight (1 - (D.weight i : ℝ) - D.weight j)
      Finset.univ (fun k u => D.basis.equivFun (formalBasisCommutator D i j) k •
        (C.coordinateField η k u - canonicalWordFrame D D.fields k u)) (by
        intro k _
        by_cases hk : D.weight k = D.weight i + D.weight j
        · have he : 1 - (D.weight k : ℝ) = 1 - (D.weight i : ℝ) - D.weight j := by
            rw [hk, Nat.cast_add]; ring
          rw [← he]
          exact fieldJetClass_const_smul U h0 (hR k) _
        · rw [formalBasisCommutator_coordinate_zero D i j k hk]
          simpa only [zero_smul] using fieldJetClass_zero U D.weight
            (1 - (D.weight i : ℝ) - D.weight j))
    apply fieldJetClass_congr U h0 hs
    intro u hu
    dsimp only
    rw [canonical_basis_bracket_expansion D Ω X hX C η hη i j hij hu]
    change _ - VectorField.lieBracket ℝ (wordBracket D.fields (modelBasisWord D i))
      (wordBracket D.fields (modelBasisWord D j)) u = _
    rw [actual_basis_bracket_eq_finiteLieField D U D.fields hMX i j hij hu]
    simp only [finiteLieField,canonicalWordFrame,smul_sub,Finset.sum_sub_distrib]
  · apply fullFieldJetClass_of_nonpos_thresholds U D.weight
      (1 - (D.weight i : ℝ) - D.weight j) _
      ((lieBracket_contDiffOn U _ _ (C.coordinateField_contDiffOn hY η hη i)
        (C.coordinateField_contDiffOn hY η hη j)).sub
        (lieBracket_contDiffOn U _ _ (hMY i) (hMY j))) _ q
    intro k
    have hk := D.weight_bound k
    have hn : D.weight k + 1 ≤ D.weight i + D.weight j := by omega
    have hr : (D.weight k : ℝ) + 1 ≤ (D.weight i : ℝ) + D.weight j := by exact_mod_cast hn
    linarith
end RothschildStein.L1
