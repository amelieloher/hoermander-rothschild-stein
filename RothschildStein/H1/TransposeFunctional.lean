-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.BarrierEstimate
public import RothschildStein.H1.OrderZeroFunctional

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ}

/-- The pointwise barrier estimate gives the full uniform
transpose estimate on smooth compact tests (BB pp. 249–250, 256–257).
P is a bounded continuous realization of the actual field operator. -/
theorem norm_test_le_operator_of_barrier
    (Ω : Opens (Fin N → ℝ))
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) {γ d : ℝ} (hγ : 0 ≤ γ) (hd : 0 ≤ d)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    (hΩ : Bornology.IsBounded (Ω : Set (Fin N → ℝ)))
    (hstrip : ∀ x ∈ Ω, -d < x j ∧ x j < d)
    (hX : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) (Ω : Set (Fin N → ℝ)))
    (P : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] BoundedContinuousFunction (Fin N → ℝ) ℝ)
    (hP : ∀ φ x, P φ x = sumSquaresWithDrift X φ x)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖ ≤
      (Real.exp (2 * γ * d) - 1) * ‖P φ‖ := by
  have hC : 0 ≤ Real.exp (2 * γ * d) - 1 := by
    have he := Real.exp_le_exp.mpr (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ) hd)
    simp only [Real.exp_zero] at he
    linarith
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg _))).mpr
  intro x
  change ‖φ x‖ ≤ _
  by_cases hx : x ∈ closure (Ω : Set (Fin N → ℝ))
  · have H := abs_le_barrier_estimate_of_barrier j hγ hbar Ω.isOpen hΩ hstrip
      (φ.contDiff.of_le (by simp)) φ.tsupport_subset hX (norm_nonneg (P φ))
      (fun z _ => by rw [← hP φ z]; exact (P φ).norm_coe_le_norm z) x hx
    simpa only [Real.norm_eq_abs, mul_comm] using H
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (subset_closure (φ.tsupport_subset ht)))
    rw [hz, norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

/-- The local bounded functional comes from the transpose field
realization and the normalized exponential drift identity
(BB Proposition 6.2, p. 250). No measure representation or
arbitrary-distribution regularity is assumed. -/
theorem exists_transposeFunctional_of_barrier
    (Ω : Opens (Fin N → ℝ))
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) {γ d : ℝ} (hγ : 0 ≤ γ) (hd : 0 ≤ d)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    (hΩ : Bornology.IsBounded (Ω : Set (Fin N → ℝ)))
    (hstrip : ∀ x ∈ Ω, -d < x j ∧ x j < d)
    (hX : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) (Ω : Set (Fin N → ℝ)))
    (P : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] BoundedContinuousFunction (Fin N → ℝ) ℝ)
    (hP : ∀ φ x, P φ x = sumSquaresWithDrift X φ x) :
    ∃ T : BoundedContinuousFunction (Fin N → ℝ) ℝ →L[ℝ] ℝ,
      ‖T‖ ≤ Real.exp (2 * γ * d) - 1 ∧ ∀ φ, T (P φ) = φ 0 := by
  apply exists_orderZeroFunctional_of_barrier Ω P
  · have he := Real.exp_le_exp.mpr (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hγ) hd)
    simp only [Real.exp_zero] at he
    linarith
  · exact norm_test_le_operator_of_barrier Ω j hγ hd hbar hΩ hstrip hX P hP

end RothschildStein.H1
