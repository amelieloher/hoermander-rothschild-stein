-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelPairings
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Integrable kernel rows from the L² sub-Markov property

Finite-measure indicators give bounded kernel integrals over compact sets. An
exhaustion by Euclidean closed balls then gives integrable rows with mass at most one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- A continuous function bounded above almost everywhere is bounded above everywhere. -/
theorem continuous_le_const_of_ae_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] {v : X → ℝ} (hv : Continuous v) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, v x ≤ C) (x : X) : v x ≤ C := by
  have heq : (fun y => min (v y) C) = v :=
    Measure.eq_of_ae_eq (hbound.mono fun y hy => min_eq_left hy)
      (hv.min continuous_const) hv
  rw [← congrFun heq x]
  exact min_le_right _ _

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hmarkov : ∀ t, 0 < t → ∀ f,
      (∀ᵐ x ∂volume, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ᵐ x ∂volume, 0 ≤ T t f x ∧ T t f x ≤ 1)

include hself hsemigroup hmarkov

/-- Sub-Markov bounds on finite-measure indicators bound every pointwise kernel set integral. -/
theorem setIntegral_heatRepresentativeKernel_le_one {t : ℝ} (ht : 0 < t)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hfinite : volume K ≠ ⊤)
    (x : Fin n → ℝ) :
    ∫ y in K, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y ≤ 1 := by
  let f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) := indicatorConstLp 2 hK hfinite (1 : ℝ)
  have hf : f =ᵐ[volume] K.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  have hfbound : ∀ᵐ y ∂volume, 0 ≤ f y ∧ f y ≤ 1 := by
    filter_upwards [hf] with y hy
    rw [hy]
    by_cases hyK : y ∈ K <;> simp [hyK]
  have hubound : ∀ᵐ y ∂volume, u t f y ≤ 1 := by
    filter_upwards [hae t ht f, hmarkov t ht f hfbound] with y hy hb
    rw [← hy]
    exact hb.2
  have hIntegral : (∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y * f y) =
      ∫ y in K, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y := by
    rw [← integral_indicator hK]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    rw [hy]
    by_cases hyK : y ∈ K <;> simp [hyK]
  calc
    (∫ y in K, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) =
        ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y * f y := hIntegral.symm
    _ = u t f x := integral_heatRepresentativeKernel_mul_L2 T u hu hae hself hsemigroup ht x f
    _ ≤ 1 := continuous_le_const_of_ae_le volume (hu t ht f) hubound x

/-- Positive kernel rows of an L² sub-Markov semigroup are integrable and have mass at most one. -/
theorem integrable_heatRepresentativeKernel_row_of_submarkov {t : ℝ} (ht : 0 < t)
    (hpos : ∀ x y, 0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y)
    (x : Fin n → ℝ) :
    Integrable (fun y => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) volume ∧
      (∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) ≤ 1 := by
  let K : ℕ → Set (Fin n → ℝ) := fun j => Metric.closedBall 0 (j : ℝ)
  have hcover : AECover volume atTop K := aecover_closedBall tendsto_natCast_atTop_atTop
  have hlocal := (memLp_evaluationKernel_of_ae_eq (heatRepresentativeEvaluation T u hu hae) x
    (ae_heatRepresentativeKernel_eq_evaluationVector T u hu hae hself hsemigroup ht x)).locallyIntegrable
      (by norm_num)
  have hbound (j : ℕ) : (∫ y in K j,
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) ≤ 1 :=
    setIntegral_heatRepresentativeKernel_le_one T u hu hae hself hsemigroup hmarkov ht
      (K j) measurableSet_closedBall (isCompact_closedBall 0 (j : ℝ)).measure_lt_top.ne x
  have hint : Integrable (fun y =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) volume :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae 1
      (fun j => hlocal.integrableOn_isCompact (isCompact_closedBall 0 (j : ℝ)))
      (Eventually.of_forall (hpos x)) (Eventually.of_forall hbound)
  exact ⟨hint, le_of_tendsto (hcover.integral_tendsto_of_countably_generated hint)
    (Eventually.of_forall hbound)⟩

end HeatKernel
