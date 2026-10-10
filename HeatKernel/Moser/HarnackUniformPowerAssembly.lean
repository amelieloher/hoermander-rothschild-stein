-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackUniformEstimateAssembly
public import HeatKernel.Moser.HarnackCoordinateComparison
public import HeatKernel.Moser.HarnackEllipticReduction
public import HeatKernel.Moser.LogarithmicUniformHarnackTails
import Mathlib.Tactic

/-! # Harnack comparisons from uniform power estimates

The logarithmic tails of nonnegative weak solutions supply a common shift on
an earlier and a later cylinder. Uniform reverse Hölder moments and reciprocal
mean values then yield the local estimates and the parabolic and elliptic
comparisons, with a comparison constant normalized as `max 1 C`.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Uniform reverse Hölder moments and reciprocal mean values combine with
the logarithmic tails of weak solutions to give local Harnack estimates. -/
theorem exists_uniform_matrix_hasHarnackCylinderEstimates_of_unshifted_power_families
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper)
    (hreverse : ∃ p₀ Cminus κminus : ℝ,
      0 < p₀ ∧ p₀ ≤ 2 ∧ 1 ≤ Cminus ∧ 0 ≤ κminus ∧
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
      ∀ σ' σ'' : ℝ, 31 / 32 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      (∫⁻ y in harnackEarlierIterationCylinder x t r σ',
        ENNReal.ofReal (u y + ε) ^ p₀ ∂μ) ^ (1 / p₀) ≤
        (ENNReal.ofReal (Cminus * (1 / (σ'' - σ')) ^ κminus) *
          (μ (harnackEarlierIterationCylinder x t r 1))⁻¹) ^ (1 / p - 1 / p₀) *
            (∫⁻ y in harnackEarlierIterationCylinder x t r σ'',
              ENNReal.ofReal (u y + ε) ^ p ∂μ) ^ (1 / p))
    (hreciprocal : ∀ p₀ : ℝ, 0 < p₀ →
      ∃ Cplus κplus : ℝ, 1 ≤ Cplus ∧ 0 ≤ κplus ∧
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
      ∀ σ' σ'' : ℝ, 9 / 10 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
      ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (1 / (u y + ε)))
        (μ.restrict (harnackLaterIterationCylinder x t r σ')) ≤
        (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
          (μ (harnackLaterIterationCylinder x t r 1))⁻¹ *
            (∫⁻ y in harnackLaterIterationCylinder x t r σ'',
              ENNReal.ofReal (1 / (u y + ε)) ^ p ∂μ)) ^ (1 / p)) :
    ∃ p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ,
      0 < p₀ ∧ p₀ ≤ 2 ∧ 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
      1 ≤ Cminus ∧ 1 ≤ Cplus ∧ 0 ≤ κminus ∧ 0 ≤ κplus ∧
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
      HasHarnackCylinderEstimates (volume.prod (CarnotPoint.volume G hq hqpos hspan))
        x t r p₀ Aminus Aplus Cminus Cplus κminus κplus u := by
  exact exists_uniform_matrix_hasHarnackCylinderEstimates_of_unshifted_families
    G hq hqpos hspan hw ell upper
    (exists_uniform_matrix_harnack_logarithmic_tails
      G hq hqpos hspan hw ell upper hell hupper) hreverse hreciprocal

end HeatKernel
