-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HarnackLocalCylinderComparison
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Uniform parabolic comparison from local estimate families

A uniform supplier of local logarithmic and power estimates for measurable
nonnegative representatives gives a uniform comparison for every original
local weak representative. The comparison constant is normalized to be at
least one. The estimate supplier remains an explicit hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- A uniform local-estimate supplier on measurable nonnegative solutions
implies parabolic Harnack for arbitrary almost-everywhere representatives. -/
theorem exists_uniform_matrix_parabolic_harnack_of_local_estimate_supplier
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper)
    {p₀ Aminus Aplus Cminus Cplus κminus κplus : ℝ}
    (hp₀ : 0 < p₀) (hp₀two : p₀ ≤ 2) (hAminus : 0 ≤ Aminus) (hAplus : 0 ≤ Aplus)
    (hCminus : 1 ≤ Cminus) (hCplus : 1 ≤ Cplus)
    (hκminus : 0 ≤ κminus) (hκplus : 0 ≤ κplus)
    (hestimates :
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
        x t r p₀ Aminus Aplus Cminus Cplus κminus κplus u) :
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ),
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
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal H *
          essInf (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackLaterTargetCylinder x t r)) := by
  obtain ⟨K, _, hcompare⟩ :=
    exists_uniform_matrix_harnackCylinder_comparison_of_local_estimates
      G hq hqpos hspan hw ell upper hell hupper hp₀ hp₀two hAminus hAplus
      hCminus hCplus hκminus hκplus
  let R := (40 / 37 : ℝ) * (25 / 24 : ℝ) ^ G.homogeneousDimension
  let Hraw := K * R ^ (1 / p₀) *
    bombieriGiustiReverseHolderConstant p₀ (Aminus * (57 / 40)) Cminus κminus
      ((63 / 64 : ℝ) - 31 / 32) *
    bombieriGiustiUniformConstant p₀ (Aplus * (113 / 96)) Cplus κplus
      ((31 / 32 : ℝ) - 9 / 10)
  refine ⟨max 1 Hraw, le_max_left _ _, ?_⟩
  intro x t r hr coeff u hn hweak ha hquad
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
  have hv := hestimates x t r hr coeff v hwm (Filter.Eventually.of_forall hwn)
    hwweak ha hquad
  have huestimates := hv.congr_ae hr huv.symm
  have hb := hcompare x t r hr coeff u hn hweak ha hquad huestimates
  exact hb.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right 1 Hraw)) _)

end HeatKernel
