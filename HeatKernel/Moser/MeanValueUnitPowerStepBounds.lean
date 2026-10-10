-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Geometry.CoordinateBall
import Mathlib.Tactic

/-! # Coefficient and measurability bounds for unit-cylinder power steps -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The cutoff energy coefficient has the quadratic power and inverse squared
gap growth needed for iteration. -/
theorem cutoff_energy_coefficient_le_power_gap_factor {C δ p : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp : 2 ≤ p) :
    2 * p * (C / δ) + (4 * p + 2) * (16 / δ ^ 2) + 1 ≤
      (100 * (C + 1)) * p ^ 2 / δ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  have heq : (2 * p * (C / δ) + (4 * p + 2) * (16 / δ ^ 2) + 1) * δ ^ 2 =
      2 * p * C * δ + 64 * p + 32 + δ ^ 2 := by
    field_simp
    ring
  rw [heq]
  have hCδ := mul_le_mul_of_nonneg_left hδ1 hC
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hpsq : 4 ≤ p ^ 2 := by nlinarith
  have hpp : 2 * p ≤ p ^ 2 := by nlinarith
  have hCp := mul_le_mul_of_nonneg_left hpsq hC
  have hCδp := mul_le_mul_of_nonneg_left hCδ (show 0 ≤ 2 * p by linarith)
  have hCpp := mul_le_mul_of_nonneg_left hpp hC
  nlinarith only [hδsq, hpsq, hpp, hCp, hCδp, hCpp, mul_nonneg hC (sq_nonneg p)]

/-- Elliptic power energy constants retain quadratic power and inverse squared
cutoff-gap growth. Ellipticity contributes a fixed multiplicative factor. -/
theorem matrix_cutoff_energy_coefficient_le_power_gap_factor {C δ p ell upper : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp : 2 ≤ p) :
    2 * max p (p / ell) * (C / δ) +
      (4 * max p (p / ell) + 2) * max (16 / δ ^ 2) (upper * (16 / δ ^ 2)) + 1 ≤
        (100 * (C + 1) * max 1 upper * (max 1 (1 / ell)) ^ 2) * p ^ 2 / δ ^ 2 := by
  let P := max p (p / ell)
  let d := max 1 upper
  let c := max 1 (1 / ell)
  have hp0 : 0 ≤ p := by linarith
  have hP : 2 ≤ P := hp.trans (le_max_left _ _)
  have hd : 1 ≤ d := le_max_left _ _
  have hPid : P = c * p := by
    dsimp only [P, c]
    rw [max_mul_of_nonneg _ _ hp0, one_mul]
    congr 1
    ring
  have hLid : max (16 / δ ^ 2) (upper * (16 / δ ^ 2)) = d * (16 / δ ^ 2) := by
    dsimp only [d]
    rw [max_mul_of_nonneg _ _ (by positivity), one_mul]
  have hbase := cutoff_energy_coefficient_le_power_gap_factor hC hδ hδ1 hP
  have hprod := mul_le_mul_of_nonneg_left hbase (show 0 ≤ d by linarith)
  have hT0 : 0 ≤ 2 * P * (C / δ) := by positivity
  have hT := mul_le_mul_of_nonneg_right hd hT0
  have hb : 2 * P * (C / δ) + (4 * P + 2) * (d * (16 / δ ^ 2)) + 1 ≤
      d * (2 * P * (C / δ) + (4 * P + 2) * (16 / δ ^ 2) + 1) := by
    nlinarith only [hT, hd]
  change 2 * P * (C / δ) + (4 * P + 2) * max (16 / δ ^ 2) (upper * (16 / δ ^ 2)) + 1 ≤ _
  rw [hLid]
  apply hb.trans
  convert hprod using 1
  rw [hPid]
  ring

/-- The weak equation supplies joint measurability on each smaller product
cylinder; continuity of the solution is unnecessary. -/
theorem IsLocalWeakSolution.aestronglyMeasurable_unit_inner_product_cylinder {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan
      coeff ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
      (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1) u)
    {r b : ℝ} (hsub : Icc (-r) b ⊆ Ioo (-1 : ℝ) 0) (hr : r ≤ 1) :
    AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
      ((volume.restrict (Icc (-r) b)).prod (volume.restrict
        (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) r : Set (Fin N → ℝ)))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hu.1.mono_measure (Measure.restrict_mono (prod_mono hsub
    (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) hr)) le_rfl)


end HeatKernel
