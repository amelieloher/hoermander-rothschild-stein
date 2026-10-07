-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformExactTimedApproximation
public import RothschildStein.G3.WeightedCoefficientNormalization
public import RothschildStein.G3.NormalizedTargetFields
public import RothschildStein.G3.TimedCoefficientBudget
public import RothschildStein.G3.UniformCoordinateTimedError
public import RothschildStein.G3.CoordinateMultiIndexBudgets
public import RothschildStein.G3.ScaledTimedRetainedLists
public import RothschildStein.G3.TimedCoefficientBudget
public import RothschildStein.G3.NumericalPrimitiveRescaling
public import RothschildStein.G3.PrimitiveFlowDisplacement
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- Bounded normalized real primitive times have a uniform actual approximation
with polynomial weighted dilation and whole-arc buffer containment. -/
theorem exists_uniform_primitive_word_approximation {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hp : ∀ i, (p i : ℕ) ≤ s)
    (i₀ : Fin a) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B) :
    ∃ A η M κ σ : ℝ, 0 < A ∧ 0 < η ∧ η ≤ 1 ∧ 0 < M ∧ 0 < κ ∧ 0 < σ ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        CoordinateMultiIndexBudget (centreBuffer K r) X (4*(s+1)^3) B →
        ∃ Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Φ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Φ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) ∧
          (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (primitiveFlowFromLieFamily D Φ κ i)
            ((centreBuffer K (r/2) : Set (Fin N → ℝ)) ×ˢ Ioo (-κ) κ)) ∧
          (∀ i x, x ∈ centreBuffer K (r/2) → primitiveFlowFromLieFamily D Φ κ i (x,0) = x ∧
            ∀ v ∈ Ioo (-κ) κ, primitiveFlowFromLieFamily D Φ κ i (x,v) ∈ centreBuffer K r ∧
              HasDerivAt (fun w => primitiveFlowFromLieFamily D Φ κ i (x,w))
                (X i (primitiveFlowFromLieFamily D Φ κ i (x,v))) v) ∧
          ∀ δ : ℝ, 0 < δ → δ < η → ∀ c : List (Fin a) → ℝ,
            (∀ I ∈ correctionWordEnumeration a s p s, |c I| ≤ δ^wordWeight p I) →
            ∃ S : List (Fin a × ℝ), S.length = enumeratedPrimitiveArcCount a s p ∧
              (∀ b ∈ S, |b.2| ≤ A*δ^(p b.1 : ℕ)) ∧
              D.basis.equivFun (normalizedWordTarget c) ∈ ball 0 σ ∧
              ∀ x ∈ K, TimedScheduleInside (primitiveFlowFromLieFamily D Φ κ)
                  (centreBuffer K (r/2)) S x ∧
                ‖runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ) S x -
                  finiteLieTimeOneMap Φ (D.basis.equivFun (normalizedWordTarget c),x)‖ ≤ M*δ^(s+1) := by
  have hR : 0 ≤ normalizedWordTargetBudget a s p := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨I,_,rfl⟩ := List.mem_map.mp hz
    exact norm_nonneg _
  obtain ⟨A,ε,M,κ,σ,hA,hε,hεone,hM,hκ,hσ,hflow⟩ :=
    exists_uniform_exactTimed_approximation_of_coordinate_partials (N := N) D hs hp i₀ hr hB hR
  obtain ⟨T,hT,_,htarget⟩ := exists_timedPrimitive_coefficient_budget D (by norm_num : (0 : ℝ) ≤ 0) hR
  obtain ⟨ν,hν,_,hsmall⟩ := exists_numerical_list_radius hσ hr (by norm_num : (0 : ℝ) ≤ 0) hT.le 0
  let η := min ε ν
  refine ⟨A,η,M,κ,σ,hA,lt_min hε hν,(min_le_left _ _).trans hεone,hM,hκ,hσ,?_⟩
  intro K X hX hbudget
  obtain ⟨Φ,hΦ,hODE,hΨsmooth,hΨODE,herror⟩ := hflow K X hX hbudget
  refine ⟨Φ,hΦ,hODE,hΨsmooth,hΨODE,?_⟩
  intro δ hδ hδη c hc
  let b := normalizeWordCoefficients p δ c
  have hb : ∀ I ∈ correctionWordEnumeration a s p s, |b I| ≤ 1 :=
    fun I hI => abs_normalizeWordCoefficients_le_one hδ c I (hc I hI)
  have hn := norm_normalizedWordTarget_le b hb
  obtain ⟨S,_,he⟩ := herror (normalizedWordTarget b) hn
  have hδε : δ < ε := hδη.trans_le (min_le_left _ _)
  have hδν : δ < ν := hδη.trans_le (min_le_right _ _)
  have hδabs : |δ| < ε := by simpa only [abs_of_pos hδ] using hδε
  have hcoords : dilatedInputCoordinates D (normalizedWordTarget b) δ =
      D.basis.equivFun (normalizedWordTarget c) :=
    dilatedInputCoordinates_normalized_source D hδ c
  have hball : D.basis.equivFun (normalizedWordTarget c) ∈ ball 0 σ := by
    rw [← hcoords]
    apply mem_ball_zero_iff.mpr
    exact ((norm_dilatedInputCoordinates_le D _ (hδabs.le.trans hεone)).trans
      (mul_le_mul_of_nonneg_left (htarget _ hn) (abs_nonneg δ))).trans_lt
        ((hsmall δ (by simpa only [abs_of_pos hδ] using hδν)).1)
  refine ⟨scaleTimedPrimitiveSchedule p δ S,(he δ hδabs).1,?_,hball,?_⟩
  · simpa only [abs_of_pos hδ] using (he δ hδabs).2.1
  · intro x hx
    simpa only [hcoords,abs_of_pos hδ] using (he δ hδabs).2.2 x hx
end RothschildStein.G3
