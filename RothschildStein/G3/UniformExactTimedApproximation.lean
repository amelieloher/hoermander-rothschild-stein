-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExactTimedApproximation
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
theorem exists_uniform_exactTimed_approximation_of_coordinate_partials {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hp : ∀ i, (p i : ℕ) ≤ s)
    (i₀ : Fin a) {r B R : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hR : 0 ≤ R) :
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
          ∀ f : formalSpan a s p, ‖f‖ ≤ R → ∃ S : List (Fin a × ℝ),
            S.length = enumeratedPrimitiveArcCount a s p ∧
            ∀ t : ℝ, |t| < η →
              (scaleTimedPrimitiveSchedule p t S).length = enumeratedPrimitiveArcCount a s p ∧
              (∀ b ∈ scaleTimedPrimitiveSchedule p t S, |b.2| ≤ A*|t| ^(p b.1 : ℕ)) ∧
              ∀ x ∈ K, TimedScheduleInside (primitiveFlowFromLieFamily D Φ κ)
                  (centreBuffer K (r/2)) (scaleTimedPrimitiveSchedule p t S) x ∧
                ‖runTimedPrimitiveSchedule (primitiveFlowFromLieFamily D Φ κ)
                    (scaleTimedPrimitiveSchedule p t S) x -
                  finiteLieTimeOneMap Φ (dilatedInputCoordinates D f t,x)‖ ≤ M*|t| ^(s+1) := by
  obtain ⟨A,hA,hfactor⟩ := exists_bounded_exact_timed_factorization hs hp i₀ R
  obtain ⟨η,M,κ,σ,hη,hηone,hM,hκ,hσ,hflow⟩ :=
    exists_uniform_scaledTimed_BCH_error_of_coordinate_partials (N := N) D hs hp hr hB hA.le hR
      (enumeratedPrimitiveArcCount a s p)
  refine ⟨A,η,M,κ,σ,hA,hη,hηone,hM,hκ,hσ,?_⟩
  intro K X hX hbudget
  obtain ⟨Φ,hΦ,hODE,hΨsmooth,hΨODE,herror⟩ := hflow K X hX hbudget
  exact ⟨Φ,hΦ,hODE,hΨsmooth,hΨODE,
    exactTimedApproximation_of_schedule_error D hfactor K (centreBuffer K (r/2))
      (primitiveFlowFromLieFamily D Φ κ) (finiteLieTimeOneMap Φ) herror⟩
end RothschildStein.G3
