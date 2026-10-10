-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ClassicalHeatEquation

/-! # Compact-test identities for classical heat solutions

Local integration by parts turns a smooth pointwise transpose equation into the
weak test identity. Divergence-free horizontal fields give the usual heat test.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators

namespace HeatKernel

open RothschildStein Hormander.Interface

/-- A smooth pointwise transpose solution annihilates the original operator on compact tests. -/
theorem integral_mul_sumSquaresWithDrift_eq_zero_of_transpose_eq_zero {n q : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (v : (Fin n → ℝ) → ℝ) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
    (heq : ∀ x ∈ Ω, sumSquaresWithDriftTranspose X v x = 0)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in (Ω : Set (Fin n → ℝ)), v x * sumSquaresWithDrift X φ x) = 0 := by
  let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hc, hs⟩
  have hibp := P2.integral_mul_sumSquaresWithDrift Ω X hX v (hv.of_le (by simp)) ψ
  change (∫ x in (Ω : Set (Fin n → ℝ)), v x * sumSquaresWithDrift X φ x) =
    ∫ x in (Ω : Set (Fin n → ℝ)), sumSquaresWithDriftTranspose X v x * φ x at hibp
  rw [hibp]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  rw [heq x hx, zero_mul]

/-- Smooth classical horizontal heat solutions satisfy the literal compact-test heat identity. -/
theorem integral_weak_heat_test_eq_zero_of_classical_equation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ z, 0 < z 0 →
      fderiv ℝ v z (leftCoordinateInclusion 1 n (fun _ => 1)) =
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v) z)
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ {z | 0 < z 0}) :
    (∫ z in {z | 0 < z 0}, v z *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) φ) z)) = 0 := by
  let Ω : Opens (Fin (1 + n) → ℝ) := ⟨{z | 0 < z 0}, isOpen_positive_time n⟩
  let X := timeSpaceFields 1 (G.horizontalFields hq)
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω :=
    fun i => (contDiff_timeSpaceFields 1 _ (G.horizontalFields_contDiff hq) i).contDiffOn
  have hdiv : ∀ i z, euclideanDivergence (X i) z = 0 := by
    apply euclideanDivergence_timeSpaceFields 1 _ (G.horizontalFields_contDiff hq)
    intro j z
    simpa only [HomogeneousGroup.horizontalFields, RothschildStein.G2.canonicalField_eq_leftField]
      using RothschildStein.G2.leftField_divergence_zero G (basisVec (Fin.castLE hq j)) z
  have hz : ∀ z ∈ Ω, sumSquaresWithDriftTranspose X v z = 0 := by
    intro z hz
    rw [sumSquaresWithDriftTranspose_eq_of_divergence_zero Ω X hX hdiv v hv hz]
    simpa only [X, timeSpaceFields_zero, timeSpaceFields_succ, fieldDerivative] using
      sub_eq_zero.mpr (hheat z hz).symm
  have hi := integral_mul_sumSquaresWithDrift_eq_zero_of_transpose_eq_zero Ω X hX v hv hz
    φ hφ hc hs
  simpa only [Ω, Opens.coe_mk, X, sumSquaresWithDrift, timeSpaceFields_zero,
    timeSpaceFields_succ, fieldDerivative] using hi

end HeatKernel
