-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalBasisBracketExpansion
public import RothschildStein.L1.WeightedFieldBrackets
public import RothschildStein.L1.WeightedFieldLinear
public import RothschildStein.L1.CoordinateFieldJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Homogeneous structure coefficients prevent a derivative loss for basis
commutators once the basis fields have the indicated finite jet weight. -/
theorem canonical_basis_bracket_weight_of_basis_weight {a s q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (hW : ∀ k, fieldJetClass (ball 0 C.radius) D.weight (-(D.weight k : ℝ)) q
      (C.coordinateField η k)) (i j : Fin (freeDimension a s p)) :
    fieldJetClass (ball 0 C.radius) D.weight
      (-(D.weight i : ℝ) - D.weight j) q
      (VectorField.lieBracket ℝ (C.coordinateField η i) (C.coordinateField η j)) := by
  let U : Opens (Fin (freeDimension a s p) → ℝ) := ⟨ball 0 C.radius,isOpen_ball⟩
  have h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ U := mem_ball_self C.radius_pos
  have hY : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordFrame D X k) Ω :=
    fun k => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D k)
  by_cases hij : D.weight i + D.weight j ≤ s
  · have hs := fieldJetClass_sum U h0 D.weight (-(D.weight i : ℝ) - D.weight j)
      Finset.univ (fun k u => D.basis.equivFun (formalBasisCommutator D i j) k •
        C.coordinateField η k u) (by
        intro k _
        by_cases hk : D.weight k = D.weight i + D.weight j
        · have hke : -(D.weight k : ℝ) = -(D.weight i : ℝ) - D.weight j := by
            rw [hk, Nat.cast_add]; ring
          rw [← hke]
          exact fieldJetClass_const_smul U h0 (hW k) _
        · rw [formalBasisCommutator_coordinate_zero D i j k hk]
          simpa only [zero_smul] using fieldJetClass_zero U D.weight
            (-(D.weight i : ℝ) - D.weight j))
    apply fieldJetClass_congr U h0 hs
    intro u hu
    simpa only [Finset.mem_univ, Finset.sum_filter] using
      canonical_basis_bracket_expansion D Ω X hX C η hη i j hij hu
  · apply fullFieldJetClass_of_nonpos_thresholds U D.weight
      (-(D.weight i : ℝ) - D.weight j) _
      (lieBracket_contDiffOn U _ _ (C.coordinateField_contDiffOn hY η hη i)
        (C.coordinateField_contDiffOn hY η hη j)) _ q
    intro k
    have hk := D.weight_bound k
    have hnat : D.weight k ≤ D.weight i + D.weight j := by omega
    have hr : (D.weight k : ℝ) ≤ (D.weight i : ℝ) + D.weight j := by exact_mod_cast hnat
    linarith
end RothschildStein.L1
