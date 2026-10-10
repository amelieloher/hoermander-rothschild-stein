-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackBombieriGiusti
public import HeatKernel.Moser.BombieriGiustiCylinderTails
public import HeatKernel.Moser.BombieriGiustiHomogeneousCylinderBounds
public import HeatKernel.Moser.BombieriGiustiReciprocalMoments
import Mathlib.Tactic

/-! # Harnack comparison on the explicit buffered cylinders

Signed logarithmic tails, the earlier reverse Hölder family, and the later
reciprocal mean-value family give the Harnack comparison. The geometric
inclusions, positive finite cylinder measures, and homogeneous source-measure
ratio are proved inputs. The remaining solution estimates are explicit
hypotheses, uniform in the positive perturbation.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The concrete cylinder bridge discharges every geometric hypothesis of the
abstract comparison. The two logarithmic-region tails may select a different
separating time for each positive perturbation, while sharing its shift. -/
theorem essSup_le_harnackCylinderConstant_mul_essInf_of_perturbed_estimates
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) (t : ℝ) {r : ℝ} (hr : 0 < r)
    {u : ℝ × CarnotPoint G hq hqpos hspan → ℝ} (hu : Measurable u)
    {p₀ Aminus Aplus Cminus Cplus κminus κplus K : ℝ}
    (hp₀ : 0 < p₀) (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (hCminus : 1 ≤ Cminus) (hCplus : 1 ≤ Cplus)
    (hκminus : 0 ≤ κminus) (hκplus : 0 ≤ κplus) (hK : 0 < K)
    (hnonneg : ∀ᵐ y ∂volume.prod (CarnotPoint.volume G hq hqpos hspan),
      y ∈ harnackEarlierIterationCylinder x t r 1 ∨
        y ∈ harnackLaterIterationCylinder x t r 1 → 0 ≤ u y)
    (hestimates : ∀ ε : ℝ, 0 < ε → ∃ τ c : ℝ,
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      let fminus := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
      let fplus := fun y => ENNReal.ofReal (Real.exp c / (u y + ε))
      t - 113 / 64 * r ^ 2 < τ ∧ τ < t - 111 / 64 * r ^ 2 ∧
      (∫⁻ y in harnackEarlierIterationCylinder x t r 1, fminus y ^ p₀ ∂μ) ≠ ⊤ ∧
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
              (∫⁻ y in harnackLaterIterationCylinder x t r σ'', fplus y ^ p ∂μ)) ^ (1 / p)) ∧
      essSup fminus (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤ ENNReal.ofReal K *
        ((μ (harnackEarlierSourceCylinder x t r))⁻¹ *
          (∫⁻ y in harnackEarlierSourceCylinder x t r, fminus y ^ p₀ ∂μ)) ^ (1 / p₀)) :
    let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
    let R := (40 / 37 : ℝ) * (25 / 24 : ℝ) ^ G.homogeneousDimension
    essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
      ENNReal.ofReal (K * R ^ (1 / p₀) *
        bombieriGiustiReverseHolderConstant p₀ (Aminus * (57 / 40)) Cminus κminus
          ((63 / 64 : ℝ) - 31 / 32) *
        bombieriGiustiUniformConstant p₀ (Aplus * (113 / 96)) Cplus κplus
          ((31 / 32 : ℝ) - 9 / 10)) *
        essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackLaterTargetCylinder x t r)) := by
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) :=
    volume.prod (CarnotPoint.volume G hq hqpos hspan)
  let : SFinite (CarnotPoint.volume G hq hqpos hspan) := by
    change SFinite (volume : Measure (Fin N → ℝ))
    infer_instance
  have hminus : 0 < μ (harnackEarlierIterationCylinder x t r 1) ∧
      μ (harnackEarlierIterationCylinder x t r 1) < ⊤ := by
    apply measure_horizontal_product_cylinder_pos_finite G hq hqpos hspan hw x
      (by nlinarith [sq_pos_of_pos hr]) (by positivity)
  have hplus : 0 < μ (harnackLaterIterationCylinder x t r 1) ∧
      μ (harnackLaterIterationCylinder x t r 1) < ⊤ := by
    apply measure_horizontal_product_cylinder_pos_finite G hq hqpos hspan hw x
      (by nlinarith [sq_pos_of_pos hr]) (by positivity)
  have hsource : 0 < μ (harnackEarlierSourceCylinder x t r) ∧
      μ (harnackEarlierSourceCylinder x t r) < ⊤ := by
    apply measure_horizontal_product_cylinder_pos_finite G hq hqpos hspan hw x
      (by nlinarith [sq_pos_of_pos hr]) (by positivity)
  have hlater := harnackLaterTargetCylinder_subset_iteration x t hr
  have hnonnegouter : ∀ᵐ y ∂μ.restrict (harnackLaterIterationCylinder x t r 1), 0 ≤ u y := by
    apply (ae_restrict_iff' (IsOpen.measurableSet (isOpen_Ioo.prod Metric.isOpen_ball))).mpr
    filter_upwards [hnonneg] with y hy hmem
    exact hy (Or.inr hmem)
  have hnonnegplus : ∀ᵐ y ∂μ.restrict (harnackLaterTargetCylinder x t r), 0 ≤ u y := by
    apply (ae_restrict_iff' (IsOpen.measurableSet (isOpen_Ioo.prod Metric.isOpen_ball))).mpr
    filter_upwards [hnonneg] with y hy hmem
    exact hy (Or.inr ((harnackIterationCylinders_mono x t hr.le
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num : (9 / 10 : ℝ) ≤ 1)).2 (hlater hmem)))
  apply essSup_ofReal_le_mul_essInf_ofReal_of_perturbed_bombieriGiusti_estimates hu
    (harnackEarlierTargetCylinder x t r) (harnackLaterTargetCylinder x t r)
    (harnackEarlierSourceCylinder x t r)
    (harnackEarlierIterationCylinder x t r) (harnackLaterIterationCylinder x t r)
    hp₀ (by positivity) (by positivity) hCminus hCplus hκminus hκplus
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hK (by positivity)
    (fun σ hσ ρ _ hσρ => (harnackIterationCylinders_mono x t hr.le
      ((by norm_num : (0 : ℝ) ≤ 31 / 32).trans hσ.1) hσρ).1)
    (fun σ hσ ρ _ hσρ => (harnackIterationCylinders_mono x t hr.le
      ((by norm_num : (0 : ℝ) ≤ 9 / 10).trans hσ.1) hσρ).2)
    hminus.1.ne' hminus.2.ne hplus.1.ne' hplus.2.ne hsource.1.ne'
    (harnackEarlierSourceCylinder_subset_iteration x t hr)
    (measure_harnackEarlier_iteration_le_source G hq hqpos hspan hw x t hr.le)
    hlater hnonnegplus
  intro ε hε
  obtain ⟨τ, c, hτlower, hτupper, hmminus, htminus, htplus, hreverse, hmean, hfixed⟩ :=
    hestimates ε hε
  have hmplus := lintegral_rescaled_reciprocal_rpow_ne_top_of_nonneg
    hplus.2.ne hnonnegouter hε hp₀.le (c := c)
  have hpositive : ∀ᵐ y ∂μ,
      y ∈ harnackEarlierIterationCylinder x t r 1 ∨
        y ∈ harnackLaterIterationCylinder x t r 1 → 0 < u y + ε := by
    filter_upwards [hnonneg] with y hy hmem
    exact add_pos_of_nonneg_of_pos (hy hmem) hε
  obtain ⟨htailminus, htailplus⟩ := harnack_iteration_exponential_tails_of_logarithmic_region_tails
    (CarnotPoint.volume G hq hqpos hspan) x t hτlower hτupper hpositive htminus htplus
  exact ⟨c, hmminus, hmplus, htailminus, htailplus, hreverse, hmean, hfixed⟩

end HeatKernel
