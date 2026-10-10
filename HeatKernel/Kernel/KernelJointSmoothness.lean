-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelWeakRegularity
public import HeatKernel.Kernel.KernelSecondProductTests

/-! # Joint smoothness from classical semigroup representatives

The two product weak heat identities follow from classical sections and compact
Fubini. Their sum supplies the two-block Hörmander equation, giving joint smoothness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- Smooth classical representatives of a self-adjoint semigroup give a jointly smooth kernel. -/
theorem contDiffOn_heatRepresentativeKernel_of_classical_representatives {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    (hheat : ∀ t, 0 < t → ∀ f x, deriv (fun s => u s f x) t =
      sumSquares (G.horizontalFields hq) (u t f) x) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2)
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) := by
  apply contDiffOn_heatRepresentativeKernel_of_two_space_integral_identity
    G hq hspan T u hu hae hself hsemigroup hsmooth
  intro φ hφ hc hs
  let k : (Fin (1 + (n + n)) → ℝ) → ℝ := fun z =>
    evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      (timeTwoSpaceCoordinates n z).1 (timeTwoSpaceCoordinates n z).2.1
      (timeTwoSpaceCoordinates n z).2.2
  let Y₁ : Fin q → (Fin (n + n) → ℝ) → Fin (n + n) → ℝ :=
    fun i => liftLeftField n (G.horizontalFields hq i)
  let Y₂ : Fin q → (Fin (n + n) → ℝ) → Fin (n + n) → ℝ :=
    fun i => liftRightField n (G.horizontalFields hq i)
  have hl := locallyIntegrableOn_coordinate_heatRepresentativeKernel T u hu hae
    (fun f => (hsmooth f).continuousOn)
  have hint (Y : Fin q → (Fin (n + n) → ℝ) → Fin (n + n) → ℝ)
      (hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)) :
      Integrable (fun z => k z * sumSquaresWithDrift (timeSpaceFields 1 Y) φ z) volume :=
    integrable_mul_sumSquaresWithDrift_compact_test hl _
      (contDiff_timeSpaceFields 1 Y hY) φ hφ hc hs
  have h₁ := integral_kernel_twoSpace_first_heat_test_eq_zero G hq T u hu hae hself hsemigroup
    hsmooth hheat φ hφ hc hs
  have h₂ := integral_kernel_twoSpace_second_heat_test_eq_zero G hq T u hu hae hself hsemigroup
    hsmooth hheat φ hφ hc hs
  have hsum : (∫ z in {z : Fin (1 + (n + n)) → ℝ | 0 < z 0},
      (k z * sumSquaresWithDrift (timeSpaceFields 1 Y₁) φ z +
        k z * sumSquaresWithDrift (timeSpaceFields 1 Y₂) φ z)) = 0 := by
    rw [integral_add (hint Y₁ (fun i => (G.horizontalFields_contDiff hq i).liftLeftField n)).integrableOn
      (hint Y₂ (fun i => (G.horizontalFields_contDiff hq i).liftRightField n)).integrableOn]
    have hs2 := congrArg₂ (fun a b : ℝ => a + b) h₁ h₂
    simp only [k, Y₁, Y₂, sumSquaresWithDrift, timeSpaceFields_zero, timeSpaceFields_succ]
    dsimp only [fieldDerivative] at hs2 ⊢
    simpa only [add_zero] using hs2
  have hpoint (z : Fin (1 + (n + n)) → ℝ) :
      k z * (2 * fderiv ℝ φ z (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
        ∑ i : Fin (q + q), fderiv ℝ
          (fun w => fderiv ℝ φ w
            (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) w)) z
          (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) z)) =
      k z * sumSquaresWithDrift (timeSpaceFields 1 Y₁) φ z +
        k z * sumSquaresWithDrift (timeSpaceFields 1 Y₂) φ z := by
    simp only [Y₁, Y₂, sumSquaresWithDrift, timeSpaceFields_zero, timeSpaceFields_succ,
      Fin.sum_univ_add, sumFields_castAdd, sumFields_natAdd, fieldDerivative]
    ring_nf
    rfl
  calc
    _ = ∫ z in {z : Fin (1 + (n + n)) → ℝ | 0 < z 0},
        (k z * sumSquaresWithDrift (timeSpaceFields 1 Y₁) φ z +
          k z * sumSquaresWithDrift (timeSpaceFields 1 Y₂) φ z) :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = 0 := hsum

end HeatKernel
