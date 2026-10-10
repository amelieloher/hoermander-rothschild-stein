-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackEstimateAssembly
public import HeatKernel.Moser.HarnackUniformComparison
import Mathlib.Tactic

/-! # Uniform assembly of the three Harnack estimate families

The three analytic suppliers are explicit hypotheses. Their constants are
selected before the cylinder, coefficient field, weak solution and positive
perturbation. Homogeneity then permits the same logarithmic shift in both
power estimates without changing any of these constants.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Uniform logarithmic tails, earlier reverse Hölder moments and later
reciprocal mean values give uniform local estimates with a shared shift. -/
theorem exists_uniform_matrix_hasHarnackCylinderEstimates_of_unshifted_families
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ)
    (hlog : ∃ Aminus Aplus : ℝ, 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
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
                  (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))))
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
  obtain ⟨Aminus, Aplus, hAminus, hAplus, hlogarithmic⟩ := hlog
  obtain ⟨p₀, Cminus, κminus, hp₀, hp₀two, hCminus, hκminus, hreverseHolder⟩ := hreverse
  obtain ⟨Cplus, κplus, hCplus, hκplus, hmeanValue⟩ := hreciprocal p₀ hp₀
  refine ⟨p₀, Aminus, Aplus, Cminus, Cplus, κminus, κplus,
    hp₀, hp₀two, hAminus, hAplus, hCminus, hCplus, hκminus, hκplus, ?_⟩
  intro x t r hr coeff u hum hn hweak ha hquad
  exact hasHarnackCylinderEstimates_of_unshifted_families
    (volume.prod (CarnotPoint.volume G hq hqpos hspan)) x t r u hp₀
    (hlogarithmic x t r hr coeff u hum hn hweak ha hquad)
    (hreverseHolder x t r hr coeff u hum hn hweak ha hquad)
    (hmeanValue x t r hr coeff u hum hn hweak ha hquad)

end HeatKernel
