-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackCylinderComparison
public import HeatKernel.Moser.HarnackLocalEstimates
public import HeatKernel.Moser.WeakSolutionMeasurableRepresentatives
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Cylinder comparison for the original local weak representative

Local almost-everywhere measurability suffices for the buffered Harnack
comparison. A measurable nonnegative representative satisfies the same weak
equation and the same logarithmic and power hypotheses. The essential extrema
are then transferred back to the original function on both target cylinders.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The literal local weak solution class supplies every measurability and
earlier moment or mean-value input of the cylinder comparison. Only the signed
logarithmic tails and two uniform power families remain analytic hypotheses. -/
theorem exists_uniform_matrix_harnackCylinder_comparison_of_local_estimates
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
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ),
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
      HasHarnackCylinderEstimates
        (volume.prod (CarnotPoint.volume G hq hqpos hspan)) x t r p₀
        Aminus Aplus Cminus Cplus κminus κplus u →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      let R := (40 / 37 : ℝ) * (25 / 24 : ℝ) ^ G.homogeneousDimension
      essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal (K * R ^ (1 / p₀) *
          bombieriGiustiReverseHolderConstant p₀ (Aminus * (57 / 40)) Cminus κminus
            ((63 / 64 : ℝ) - 31 / 32) *
          bombieriGiustiUniformConstant p₀ (Aplus * (113 / 96)) Cplus κplus
            ((31 / 32 : ℝ) - 9 / 10)) *
          essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackLaterTargetCylinder x t r)) := by
  obtain ⟨K, hK, hcompare⟩ :=
    exists_uniform_matrix_harnackCylinder_comparison_of_logarithmic_and_power_estimates
      G hq hqpos hspan hw ell upper hell hupper hp₀ hp₀two hAminus hAplus
      hCminus hCplus hκminus hκplus
  refine ⟨K, hK, ?_⟩
  intro x t r hr coeff u hn hweak ha hquad hestimates
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) :=
    volume.prod (CarnotPoint.volume G hq hqpos hspan)
  let D := Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)
  have hball :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x (2 * r) : Set (Fin N → ℝ)) =
        horizontalBall (G.horizontalFields hq) x (2 * r) :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x (2 * r)
  have hncoord : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo (t - 4 * r ^ 2) t ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)),
      0 ≤ u (z.1, z.2) := by
    have hn' := hn
    change ∀ᵐ z ∂(volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo (t - 4 * r ^ 2) t ×ˢ
        (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x (2 * r) : Set (Fin N → ℝ))),
      0 ≤ u z at hn'
    rw [hball] at hn'
    exact hn'.mono fun _ hz => hz
  obtain ⟨w, hwm, hwn, huw, hwweak⟩ :=
    hweak.exists_nonnegative_measurable_representative hncoord
  let v : ℝ × CarnotPoint G hq hqpos hspan → ℝ := fun z => w z
  have huv : u =ᵐ[μ.restrict D] v := by
    change (fun z : ℝ × (Fin N → ℝ) => u z) =ᵐ[
      (volume : Measure (ℝ × (Fin N → ℝ))).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ
          (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x (2 * r) : Set (Fin N → ℝ)))]
            (fun z => w z)
    rw [hball]
    exact huw
  have hv := hestimates.congr_ae hr huv
  have hb := hcompare x t r hr coeff v hwm (Filter.Eventually.of_forall hwn)
    hwweak ha hquad hv
  obtain ⟨hminus, hplus⟩ := harnackTargetCylinders_subset_outer x t hr
  have hs := essSup_congr_ae ((ae_restrict_of_ae_restrict_of_subset hminus huv).mono
    fun _ hy => congrArg ENNReal.ofReal hy)
  have hi := essInf_congr_ae ((ae_restrict_of_ae_restrict_of_subset hplus huv).mono
    fun _ hy => congrArg ENNReal.ofReal hy)
  dsimp only at hb ⊢
  rw [hs, hi]
  exact hb

end HeatKernel
