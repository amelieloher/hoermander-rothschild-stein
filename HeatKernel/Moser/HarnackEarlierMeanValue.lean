-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueMatrixNestedScaling
public import HeatKernel.Moser.BombieriGiustiNonnegativeNorms
public import HeatKernel.Moser.BombieriGiustiCylinders
public import HeatKernel.Moser.WeakSolutionAffine
public import HeatKernel.Moser.MeanValueWeakRestriction
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # The earlier mean-value input for uniformly elliptic matrix weak solutions

The fixed source cylinder has spatial radius `6r/5` and time length `37r²/32`.
Its upper subcylinder has radius `r` and time length `35r²/32`. These fixed
ratios specialize the normalized positive-power mean-value theorem, with a
constant chosen before the radius, location, perturbation and logarithmic shift.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The uniformly elliptic matrix weak equation supplies the earlier fixed-exponent mean-value
bound in precisely the normalized moment convention of the Harnack bridge. -/
theorem exists_uniform_matrix_harnackEarlier_mean_value
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p : ℝ} (hp : 0 < p)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ),
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (harnackEarlierSourceCylinder x t r), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2), isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (6 / 5 * r),
          isOpen_horizontalBall G hq hqpos hspan x (6 / 5 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal K * ((μ (harnackEarlierSourceCylinder x t r))⁻¹ *
          (∫⁻ y in harnackEarlierSourceCylinder x t r, ENNReal.ofReal (u y) ^ p ∂μ)) ^ (1 / p) := by
  obtain ⟨K, hK, hmean⟩ := exists_uniform_matrix_nested_cylinder_positive_power_mean_value
    G hq hqpos hspan hw hp (τ := 925 / 1152) (θ := 875 / 1152) (ρ := 5 / 6)
    (by norm_num) (by norm_num) (by norm_num) ell upper hell hupper
  refine ⟨K, hK, ?_⟩
  intro x t r hr coeff u hn hweak ha hquad
  let v : ℝ × (Fin N → ℝ) → ℝ := fun z => u z
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) :=
    volume.prod (CarnotPoint.volume G hq hqpos hspan)
  have hbottom : (t - 63 / 32 * r ^ 2) - (6 / 5 * r) ^ 2 * (925 / 1152) =
      t - 25 / 8 * r ^ 2 := by ring
  have hinner : (t - 63 / 32 * r ^ 2) - (6 / 5 * r) ^ 2 * (875 / 1152) =
      t - 49 / 16 * r ^ 2 := by ring
  have hradius : (6 / 5 * r) * (5 / 6) = r := by ring
  have hball (s : ℝ) :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x s : Set (Fin N → ℝ)) =
        horizontalBall (G.horizontalFields hq) x s :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x s
  have hbound := hmean (t - 63 / 32 * r ^ 2) x (6 / 5 * r) (by positivity) v coeff
    (by
      have hn' := hn
      change ∀ᵐ z ∂(volume : Measure (ℝ × (Fin N → ℝ))).restrict
        (Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ
          (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x (6 / 5 * r) : Set (Fin N → ℝ))),
          0 ≤ v z at hn'
      simpa only [hbottom, hball] using hn')
    (by simpa only [hbottom] using hweak) ha hquad
  simp only [hbottom, hinner, hradius] at hbound
  have hb : eLpNormEssSup u (μ.restrict (harnackEarlierUpperCylinder x t r)) ≤
      ENNReal.ofReal K * eLpNorm u (ENNReal.ofReal p)
        ((μ (harnackEarlierSourceCylinder x t r))⁻¹ •
          μ.restrict (harnackEarlierSourceCylinder x t r)) := by
    dsimp only [μ, harnackEarlierUpperCylinder, harnackEarlierSourceCylinder]
    simp only [hball]
    change eLpNormEssSup v ((volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo (t - 49 / 16 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ
        horizontalBall (G.horizontalFields hq) x r)) ≤ ENNReal.ofReal K *
      eLpNorm v (ENNReal.ofReal p)
        (((volume : Measure (ℝ × (Fin N → ℝ)))
          (Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ
          horizontalBall (G.horizontalFields hq) x (6 / 5 * r)))⁻¹ •
            (volume : Measure (ℝ × (Fin N → ℝ))).restrict
              (Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ
              horizontalBall (G.horizontalFields hq) x (6 / 5 * r)))
    exact hbound
  have hm : AEStronglyMeasurable u (μ.restrict (harnackEarlierSourceCylinder x t r)) := by
    dsimp only [μ, harnackEarlierSourceCylinder]
    simp only [hball]
    change AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z)
      (volume.restrict (Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ
        horizontalBall (G.horizontalFields hq) x (6 / 5 * r)))
    exact hweak.1
  have hnsource : ∀ᵐ y ∂μ.restrict (harnackEarlierSourceCylinder x t r), 0 ≤ u y := hn
  have htargetsource := (harnackEarlierTargetCylinder_subset_upper x t r).trans
    (harnackEarlierUpperCylinder_subset_source x t hr)
  have hntarget := ae_restrict_of_ae_restrict_of_subset htargetsource hnsource
  change essSup (fun y => ENNReal.ofReal (u y)) (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
    ENNReal.ofReal K * ((μ (harnackEarlierSourceCylinder x t r))⁻¹ *
      (∫⁻ y in harnackEarlierSourceCylinder x t r, ENNReal.ofReal (u y) ^ p ∂μ)) ^ (1 / p)
  rw [essSup_ofReal_eq_eLpNormEssSup_of_nonneg hntarget,
    ← eLpNorm_normalized_restrict_eq_moment_of_nonneg hp hm hnsource]
  exact (eLpNormEssSup_mono_measure u (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono (harnackEarlierTargetCylinder_subset_upper x t r) le_rfl))).trans hb

/-- The constant for the earlier mean-value input is uniform in positive
perturbations and exponential shifts of an almost-everywhere nonnegative
uniformly elliptic matrix solution. -/
theorem exists_uniform_matrix_harnackEarlier_shifted_mean_value
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p : ℝ} (hp : 0 < p)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ),
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (harnackEarlierSourceCylinder x t r), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2), isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (6 / 5 * r),
          isOpen_horizontalBall G hq hqpos hspan x (6 / 5 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ε : ℝ, 0 < ε → ∀ c : ℝ,
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      let f := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
      essSup f (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal K * ((μ (harnackEarlierSourceCylinder x t r))⁻¹ *
          (∫⁻ y in harnackEarlierSourceCylinder x t r, f y ^ p ∂μ)) ^ (1 / p) := by
  obtain ⟨K, hK, hmean⟩ := exists_uniform_matrix_harnackEarlier_mean_value
    G hq hqpos hspan hw hp ell upper hell hupper
  refine ⟨K, hK, ?_⟩
  intro x t r hr coeff u hn hweak ha hquad ε hε c
  have hshift := hweak.affine G hq hqpos hw hspan 1 ε
  simp only [one_mul] at hshift
  have hscale := hshift.const_mul G hq hqpos hw hspan (Real.exp (-c))
  exact hmean x t r hr coeff (fun y => Real.exp (-c) * (u y + ε))
    (hn.mono fun _ hy => mul_nonneg (Real.exp_pos _).le (add_nonneg hy hε.le)) hscale ha hquad

/-- A solution on the full Harnack cylinder supplies the earlier mean-value
input for all positive perturbations and all logarithmic shifts. Restriction
of the equation and of the nonnegativity assumption is part of the conclusion. -/
theorem exists_uniform_matrix_harnackEarlier_shifted_mean_value_on_outer_cylinder
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p : ℝ} (hp : 0 < p)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
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
      ∀ ε : ℝ, 0 < ε → ∀ c : ℝ,
      let μ := volume.prod (CarnotPoint.volume G hq hqpos hspan)
      let f := fun y => ENNReal.ofReal (Real.exp (-c) * (u y + ε))
      essSup f (μ.restrict (harnackEarlierTargetCylinder x t r)) ≤
        ENNReal.ofReal K * ((μ (harnackEarlierSourceCylinder x t r))⁻¹ *
          (∫⁻ y in harnackEarlierSourceCylinder x t r, f y ^ p ∂μ)) ^ (1 / p) := by
  obtain ⟨K, hK, hmean⟩ := exists_uniform_matrix_harnackEarlier_shifted_mean_value
    G hq hqpos hspan hw hp ell upper hell hupper
  refine ⟨K, hK, ?_⟩
  intro x t r hr coeff u hn hweak ha hquad ε hε c
  have hI : Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2) ⊆
      Ioo (t - 4 * r ^ 2) t := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2, sq_pos_of_pos hr]
  have hball (s : ℝ) :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x s : Set (Fin N → ℝ)) =
        horizontalBall (G.horizontalFields hq) x s :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x s
  have hU : horizontalBall (G.horizontalFields hq) x (6 / 5 * r) ⊆
      horizontalBall (G.horizontalFields hq) x (2 * r) := by
    rw [← hball, ← hball]
    exact Metric.ball_subset_ball (by linarith)
  have hsource : harnackEarlierSourceCylinder x t r ⊆
      Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r) :=
    prod_mono hI (Metric.ball_subset_ball (by linarith))
  exact hmean x t r hr coeff u (ae_restrict_of_ae_restrict_of_subset hsource hn)
    (hweak.mono hI hU) ha hquad ε hε c

end HeatKernel
