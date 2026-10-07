-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.TransposeFunctional
public import RothschildStein.H1.TestOperator
public import RothschildStein.H1.SmoothDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ}

/-- The local order-zero fundamental distribution exists for the
transpose realization. Choosing drift-reversed fields gives L T = delta
at zero under the normalized exponential drift identity
(BB Proposition 6.2, p. 250; Proposition 6.9, p. 257). -/
theorem exists_localFundamentalDistribution_of_barrier
    (Ω : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (j : Fin N) {γ d : ℝ} (hγ : 0 ≤ γ) (hd : 0 ≤ d)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    (hΩ : Bornology.IsBounded (Ω : Set (Fin N → ℝ)))
    (hstrip : ∀ x ∈ Ω, -d < x j ∧ x j < d) :
    ∃ T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ,
      ‖T‖ ≤ Real.exp (2 * γ * d) - 1 ∧
      ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
        smoothOrderZeroDistribution Ω T (sumSquaresTest Ω X hX φ) = φ 0 := by
  have hXd : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) (Ω : Set (Fin N → ℝ)) :=
    fun i => (hX i.succ).differentiableOn (by simp)
  obtain ⟨T, hT, he⟩ := exists_transposeFunctional_of_barrier Ω j hγ hd hbar hΩ hstrip
    hXd (sumSquaresBoundedTest Ω X hX) (sumSquaresBoundedTest_apply Ω X hX)
  refine ⟨T, hT, fun φ => ?_⟩
  rw [smoothOrderZeroDistribution_apply]
  exact he φ

/-- The constructed distribution satisfies the order-zero bound on all
smooth tests (BB p. 250). -/
theorem abs_smoothOrderZeroDistribution_le
    (Ω : Opens (Fin N → ℝ))
    (T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ)
    {C : ℝ} (hT : ‖T‖ ≤ C) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    |smoothOrderZeroDistribution Ω T φ| ≤
      C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ := by
  rw [smoothOrderZeroDistribution_apply, ← Real.norm_eq_abs]
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

end RothschildStein.H1
