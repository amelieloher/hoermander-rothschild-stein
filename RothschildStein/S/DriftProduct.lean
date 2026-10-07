-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Leibniz
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresTranspose
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.Definitions.sumSquaresWithDriftTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n q : ℕ}

/-- The weak product identity for the operator with index-zero drift (BB (8.62), p. 375; p. 590). -/
theorem integral_sumSquaresWithDrift_product
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (f a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (G : Fin (q + 1) → (Fin n → ℝ) → ℝ) (H : Fin q → (Fin n → ℝ) → ℝ)
    (h₁ : ∀ i, hasWeakWordDeriv X Ω [i] f (G i))
    (h₂ : ∀ i : Fin q, hasWeakWordDeriv X Ω [i.succ,i.succ] f (H i))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)),
      ((G 0 x + ∑ i, H i x) * a x + f x * sumSquaresWithDrift X a x +
        2 * ∑ i : Fin q, G i.succ x * fieldDerivative (X i.succ) a x) * ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), f x * a x * sumSquaresWithDriftTranspose X ψ x := by
  classical
  let P : Fin q → (Fin n → ℝ) → ℝ := fun i x =>
    H i x * a x + 2 * G i.succ x * fieldDerivative (X i.succ) a x +
      f x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) a) x
  let P₀ : (Fin n → ℝ) → ℝ := fun x => G 0 x * a x + f x * fieldDerivative (X 0) a x
  have hs : ∀ i, hasWeakWordDeriv X Ω [i.succ,i.succ] (fun x => f x * a x) (P i) :=
    fun i => hasWeakWordDeriv_mul_square X Ω hX i.succ f (G i.succ) (H i) a ha
      (h₁ i.succ) (h₂ i)
  have h₀ : hasWeakWordDeriv X Ω [0] (fun x => f x * a x) P₀ :=
    hasWeakWordDeriv_mul_one X Ω hX 0 f (G 0) a ha (h₁ 0)
  have hl : ∀ i, IntegrableOn (fun x => P i x * ψ x) (Ω : Set (Fin n → ℝ)) :=
    fun i => (integrable_mul_test Ω (hs i).2.1 ψ).integrableOn
  have hr : ∀ i : Fin q, IntegrableOn (fun x => f x * a x *
      fieldTranspose (X i.succ) (fieldTranspose (X i.succ) ψ) x) (Ω : Set (Fin n → ℝ)) := by
    intro i
    have ht := (integrable_mul_test Ω (hs i).1
      (wordTransposeTest Ω X hX [i.succ,i.succ] ψ)).integrableOn
        (s := (Ω : Set (Fin n → ℝ)))
    simpa only [wordTransposeTest_apply, wordTranspose] using ht
  have hl₀ := (integrable_mul_test Ω h₀.2.1 ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  have hr₀ := (integrable_mul_test Ω h₀.1
    (wordTransposeTest Ω X hX [0] ψ)).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  simp only [wordTransposeTest_apply, wordTranspose] at hr₀
  have hformula : ∀ x, (G 0 x + ∑ i, H i x) * a x + f x * sumSquaresWithDrift X a x +
      2 * ∑ i : Fin q, G i.succ x * fieldDerivative (X i.succ) a x = P₀ x + ∑ i, P i x := by
    intro x
    simp only [P, P₀, sumSquaresWithDrift, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum, mul_add, add_mul]
    simp only [mul_assoc, mul_comm, mul_left_comm]
    ring
  simp_rw [hformula, add_mul, Finset.sum_mul]
  rw [integral_add hl₀ (integrable_finsetSum _ (fun i _ => hl i)),
    integral_finsetSum _ (fun i _ => hl i)]
  simp_rw [show ∀ i, (∫ x in (Ω : Set (Fin n → ℝ)), P i x * ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)),
        f x * a x * fieldTranspose (X i.succ) (fieldTranspose (X i.succ) ψ) x from
    fun i => by simpa only [wordTranspose] using (hs i).2.2 ψ]
  rw [show (∫ x in (Ω : Set (Fin n → ℝ)), P₀ x * ψ x) =
    ∫ x in (Ω : Set (Fin n → ℝ)), f x * a x * fieldTranspose (X 0) ψ x from
      by simpa only [wordTranspose] using h₀.2.2 ψ]
  rw [← integral_finsetSum _ (fun i _ => hr i),
    ← integral_add hr₀ (integrable_finsetSum _ (fun i _ => hr i))]
  simp only [sumSquaresWithDriftTranspose, Finset.mul_sum, mul_add]

end RothschildStein.S
