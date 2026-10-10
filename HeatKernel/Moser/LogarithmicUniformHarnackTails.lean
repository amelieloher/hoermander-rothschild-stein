-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicUniformRegionTails
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Uniform logarithmic tails for nonnegative matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- At almost every separating time, one logarithmic shift gives both weak-L¹
tails, uniformly over cylinders, coefficients, solutions and positive shifts. -/
theorem exists_uniform_matrix_harnack_logarithmic_tails_ae
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ Aminus Aplus : ℝ, 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ε : ℝ, 0 < ε →
      ∀ᵐ τ ∂volume.restrict (Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2)),
      ∃ c : ℝ,
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ∩
              {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r))) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ∩
              {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))) := by
  obtain ⟨Aminus, Aplus, hAminus, hAplus, htails⟩ :=
    exists_uniform_matrix_logarithmic_region_tails_ae G hq hqpos hspan hw ell upper hell hupper
  refine ⟨Aminus, Aplus, hAminus, hAplus, ?_⟩
  intro x t r hr coeff u hum hn hweak ha hquad ε hε
  exact htails x t r hr (t - 225 / 64 * r^2) (5 / 4 * r)
    (by nlinarith [sq_nonneg r]) (by nlinarith [sq_nonneg r]) le_rfl
    (by nlinarith [hr.le]) coeff u hum hn hweak ha hquad ε hε

/-- One separating time and one logarithmic shift give both weak-L¹ tails,
with constants uniform over cylinders, coefficients, solutions and positive shifts. -/
theorem exists_uniform_matrix_harnack_logarithmic_tails
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ Aminus Aplus : ℝ, 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ε : ℝ, 0 < ε → ∃ τ c : ℝ,
        t - 113 / 64 * r ^ 2 < τ ∧ τ < t - 111 / 64 * r ^ 2 ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ∩
              {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r))) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ∩
              {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))) := by
  obtain ⟨Aminus, Aplus, hAminus, hAplus, htails⟩ :=
    exists_uniform_matrix_harnack_logarithmic_tails_ae G hq hqpos hspan hw ell upper hell hupper
  refine ⟨Aminus, Aplus, hAminus, hAplus, ?_⟩
  intro x t r hr coeff u hum hn hweak ha hquad ε hε
  have hpos : volume (Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    apply ne_of_gt (ENNReal.ofReal_pos.mpr _)
    nlinarith [sq_pos_of_pos hr]
  obtain ⟨τ, hτ, c, hminus, hplus⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (htails x t r hr coeff u hum hn hweak ha hquad ε hε)
  exact ⟨τ, c, hτ.1, hτ.2, hminus, hplus⟩

end HeatKernel
