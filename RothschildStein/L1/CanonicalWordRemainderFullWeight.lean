-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalBasisRemainderFullWeight
public import RothschildStein.L1.CanonicalWordBasisExpansion
public import RothschildStein.L1.CanonicalHighWordWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Every retained actual word remainder has its full strict word weight,
by the shared homogeneous basis coefficients of actual and model words
(BB Theorem 10.28, pp. 506–509). -/
theorem canonical_retained_word_remainder_full_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    fullFieldJetClass (ball 0 C.radius) D.weight (1 - (wordWeight p I : ℝ))
      (fun u => canonicalWordRemainder D X C I (η,u)) := by
  let U : Opens (Fin (freeDimension a s p) → ℝ) := ⟨ball 0 C.radius,isOpen_ball⟩
  have h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ U := mem_ball_self C.radius_pos
  have hMX : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (D.fields k) U :=
    fun k => (freeModel_fields_smooth D k).contDiffOn
  intro q
  have hs := fieldJetClass_sum U h0 D.weight (1 - (wordWeight p I : ℝ)) Finset.univ
    (fun k u => D.basis.equivFun (wordLieElement I) k •
      (C.coordinateField η k u - canonicalWordFrame D D.fields k u)) (by
      intro k _
      by_cases hk : D.weight k = wordWeight p I
      · have ht := fieldJetClass_const_smul U h0
          (canonical_basis_remainder_full_weight D Ω X hX C η hη k q)
          (D.basis.equivFun (wordLieElement I) k)
        simpa only [hk] using ht
      · rw [wordLieElement_basis_coordinate_zero D I k hk]
        simpa only [zero_smul] using fieldJetClass_zero (p := q) U D.weight
          (1 - (wordWeight p I : ℝ)))
  apply fieldJetClass_congr U h0 hs
  intro u hu
  dsimp only [canonicalWordRemainder]
  rw [canonical_wordBracket_basis_expansion D Ω X hX C η hη I hI hu,
    wordBracket_eq_formal_basis_sum D U D.fields hMX I hI hu]
  simp only [canonicalWordFrame,smul_sub,Finset.sum_sub_distrib]

/-- The strict approximation weight holds for every word. Vanishing
at zero is exported separately and only through the retained cutoff. -/
theorem canonical_word_remainder_full_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) :
    fullFieldJetClass (ball 0 C.radius) D.weight (1 - (wordWeight p I : ℝ))
      (fun u => canonicalWordRemainder D X C I (η,u)) := by
  by_cases hI : wordWeight p I ≤ s
  · exact canonical_retained_word_remainder_full_weight D Ω X hX C η hη I hI
  · exact canonical_high_word_remainder_weight D Ω X hX C η hη I (by omega)
end RothschildStein.L1
