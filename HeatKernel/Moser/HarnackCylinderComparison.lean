-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackCylinderBombieriGiusti
public import HeatKernel.Moser.HarnackEarlierMeanValue
public import HeatKernel.Moser.HarnackEarlierMoments
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # The uniformly elliptic matrix cylinder comparison

The local weak equation supplies the earlier finite moment and the fixed-power
mean-value estimate. The signed logarithmic tails, earlier reverse Hölder
family, and later reciprocal mean-value family remain explicit hypotheses.
Their constants and the resulting comparison constant are independent of the
solution, center, radius, perturbation and logarithmic shift.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The uniformly elliptic matrix weak equation discharges the earlier moment and mean-value
inputs of the cylinder comparison, leaving precisely the logarithmic and
two uniform power-family estimates as analytic hypotheses. -/
theorem exists_uniform_matrix_harnackCylinder_comparison_of_logarithmic_and_power_estimates
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper)
    {p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ}
    (hp₀ : 0 < p₀) (hp₀two : p₀ ≤ 2) (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (hCminus : 1 ≤ Cminus) (hCplus : 1 ≤ Cplus)
    (hκminus : 0 ≤ κminus) (hκplus : 0 ≤ κplus) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      (∀ ε : ℝ, 0 < ε → ∃ τ c : ℝ,
        let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
        let fminus := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
        let fplus := fun y => ENNReal.ofReal (Real.exp c / (u y + ε))
        t - 113 / 64 * r ^ 2 < τ ∧ τ < t - 111 / 64 * r ^ 2 ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          μ ((Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r)) ∩
            {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
              μ (Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r))) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          μ ((Ioo τ t ×ˢ Metric.ball x (5 / 4 * r)) ∩
            {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
              μ (Ioo τ t ×ˢ Metric.ball x (5 / 4 * r))) ∧
        (∀ σ' σ'' : ℝ, 31 / 32 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
          ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
          (∫⁻ y in harnackEarlierIterationCylinder x t r σ', fminus y ^ p₀ ∂μ) ^ (1 / p₀) ≤
            (ENNReal.ofReal (Cminus * (1 / (σ'' - σ')) ^ κminus) *
              (μ (harnackEarlierIterationCylinder x t r 1))⁻¹) ^ (1 / p - 1 / p₀) *
                (∫⁻ y in harnackEarlierIterationCylinder x t r σ'', fminus y ^ p ∂μ) ^ (1 / p)) ∧
        (∀ σ' σ'' : ℝ, 9 / 10 ≤ σ' → σ' < σ'' → σ'' ≤ 1 →
          ∀ p : ℝ, 0 < p → p ≤ p₀ / 2 →
          essSup fplus (μ.restrict (harnackLaterIterationCylinder x t r σ')) ≤
            (ENNReal.ofReal (Cplus * (1 / (σ'' - σ')) ^ κplus) *
              (μ (harnackLaterIterationCylinder x t r 1))⁻¹ *
                (∫⁻ y in harnackLaterIterationCylinder x t r σ'', fplus y ^ p ∂μ)) ^ (1 / p))) →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      let R := (40 / 37 : ℝ) * (25 / 24 : ℝ) ^ G.homogeneousDimension
      essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal (K * R ^ (1 / p₀) *
          bombieriGiustiReverseHolderConstant p₀ (Aminus * (57 / 40)) Cminus κminus
            ((63 / 64 : ℝ) - 31 / 32) *
          bombieriGiustiUniformConstant p₀ (Aplus * (113 / 96)) Cplus κplus
            ((31 / 32 : ℝ) - 9 / 10)) *
          essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackLaterTargetCylinder x t r)) := by
  obtain ⟨K, hK, hfixed⟩ := exists_uniform_matrix_harnackEarlier_shifted_mean_value_on_outer_cylinder
    G hq hqpos hspan hw hp₀ ell upper hell hupper
  refine ⟨K, hK, ?_⟩
  intro x t r hr coeff u hu hn hweak ha hquad hestimates
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) :=
    volume.prod (CarnotPoint.volume G hq hqpos hspan)
  have hballs : Metric.ball x (5 / 4 * r) ⊆ Metric.ball x (2 * r) :=
    Metric.ball_subset_ball (by linarith)
  have hearlier : harnackEarlierIterationCylinder x t r 1 ⊆
      Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
    intro z hz
    dsimp only [harnackEarlierIterationCylinder] at hz
    simp only [one_pow, mul_one] at hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr],
      by nlinarith [hz.1.2, sq_pos_of_pos hr]⟩, hballs hz.2⟩
  have hlater : harnackLaterIterationCylinder x t r 1 ⊆
      Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) := by
    intro z hz
    dsimp only [harnackLaterIterationCylinder] at hz
    simp only [one_pow, mul_one] at hz
    exact ⟨⟨by nlinarith [hz.1.1, sq_pos_of_pos hr], hz.1.2⟩, hballs hz.2⟩
  have hnonneg : ∀ᵐ y ∂μ, y ∈ harnackEarlierIterationCylinder x t r 1 ∨
      y ∈ harnackLaterIterationCylinder x t r 1 → 0 ≤ u y := by
    filter_upwards [ae_imp_of_ae_restrict hn] with y hy hmem
    rcases hmem with hm | hm
    · exact hy (hearlier hm)
    · exact hy (hlater hm)
  apply essSup_le_harnackCylinderConstant_mul_essInf_of_perturbed_estimates
    G hq hqpos hspan hw x t hr hu hp₀ hAminus hAplus hCminus hCplus hκminus hκplus hK hnonneg
  intro ε hε
  obtain ⟨τ, c, hτlower, hτupper, htminus, htplus, hreverse, hreciprocal⟩ := hestimates ε hε
  have hmoment : (∫⁻ y in harnackEarlierIterationCylinder x t r 1,
      ENNReal.ofReal (Real.exp (-c) * (u y + ε)) ^ p₀ ∂μ) ≠ ⊤ := by
    change (∫⁻ y in (harnackEarlierIterationCylinder (E := CarnotPoint G hq hqpos hspan)
      x t r 1 : Set (ℝ × (Fin N → ℝ))), ENNReal.ofReal (Real.exp (-c) * (u y + ε)) ^ p₀
        ∂(volume : Measure (ℝ × (Fin N → ℝ)))) ≠ ⊤
    exact hweak.lintegral_shifted_harnackEarlier_rpow_ne_top
      G hq hqpos hspan hw x t hr hp₀ hp₀two ε c
  exact ⟨τ, c, hτlower, hτupper, hmoment, htminus, htplus, hreverse, hreciprocal,
    hfixed x t r hr coeff u hn hweak ha hquad ε hε c⟩

end HeatKernel
