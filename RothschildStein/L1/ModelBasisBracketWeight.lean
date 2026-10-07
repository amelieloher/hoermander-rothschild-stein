-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalBasisBracketWeight
public import RothschildStein.G3.ModelPackage
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- The model basis commutator filtration closes with the same formal
homogeneous coefficients used for the actual canonical frame. -/
theorem model_basis_bracket_weight_of_basis_weight {a s q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ Ω)
    (hW : ∀ k, fieldJetClass Ω D.weight (-(D.weight k : ℝ)) q
      (canonicalWordFrame D D.fields k)) (i j : Fin (freeDimension a s p)) :
    fieldJetClass Ω D.weight (-(D.weight i : ℝ) - D.weight j) q
      (VectorField.lieBracket ℝ (canonicalWordFrame D D.fields i)
        (canonicalWordFrame D D.fields j)) := by
  let U := Ω
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields i) Ω :=
    fun i => (freeModel_fields_smooth D i).contDiffOn
  have hY : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordFrame D D.fields k) Ω :=
    fun k => G1.wordBracket_contDiffOn Ω.isOpen D.fields hX (modelBasisWord D k)
  by_cases hij : D.weight i + D.weight j ≤ s
  · have hs := fieldJetClass_sum U h0 D.weight (-(D.weight i : ℝ) - D.weight j)
      Finset.univ (fun k u => D.basis.equivFun (formalBasisCommutator D i j) k •
        canonicalWordFrame D D.fields k u) (by
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
    simpa only [finiteLieField, canonicalWordFrame] using
      actual_basis_bracket_eq_finiteLieField D Ω D.fields hX i j hij hu
  · apply fullFieldJetClass_of_nonpos_thresholds U D.weight
      (-(D.weight i : ℝ) - D.weight j) _
      (lieBracket_contDiffOn U _ _ (hY i)
        (hY j)) _ q
    intro k
    have hk := D.weight_bound k
    have hnat : D.weight k ≤ D.weight i + D.weight j := by omega
    have hr : (D.weight k : ℝ) ≤ (D.weight i : ℝ) + D.weight j := by exact_mod_cast hnat
    linarith
end RothschildStein.L1
