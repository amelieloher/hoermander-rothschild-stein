-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotBoundaryClosure
public import HeatKernel.Poincare.WhitneyWeakPoincare
public import HeatKernel.Poincare.NormalizedPowerEnergy

/-! Finite local energy costs controlling smooth Whitney averaging oscillations. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal

namespace HeatKernel

/-- Smoothness inside the original ball constructs each finite normalized Whitney cost
and proves its exact energy identity and twentyfold averaging oscillation estimate. -/
theorem exists_boundaryBall_energy_cost {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z : CarnotPoint G hq hqpos hspan} {r κ p : ℝ} (hr : 0 < r) (hκ : 80 < κ)
    (hz : z ∈ ball x r) (hp : 1 ≤ p) (u : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r)) :
    let a := infDist z (ball x r)ᶜ / κ
    let A := horizontalBall (G.horizontalFields hq) z a
    let D := horizontalBall (G.horizontalFields hq) z (80 * a)
    let I := ∫⁻ w in D, ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u w ^ p)
    ∃ h : ℝ≥0, (h : ℝ≥0∞) = (I / volume A) ^ (1 / p) ∧
      volume A * ((h ^ p : ℝ≥0) : ℝ≥0∞) = I ∧
      eLpNorm (fun y => u y - ⨍ w in horizontalBall (G.horizontalFields hq) z (20 * a), u w)
        (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) z (20 * a))) ≤
        ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a))) *
          volume A ^ (1 / p) * h := by
  let a := infDist z (ball x r)ᶜ / κ
  let A := horizontalBall (G.horizontalFields hq) z a
  let D := horizontalBall (G.horizontalFields hq) z (80 * a)
  let I := ∫⁻ w in D, ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u w ^ p)
  let g := horizontalGradientNorm (G.horizontalFields hq) u
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hgn : ∀ w, 0 ≤ g w := fun _ => Real.sqrt_nonneg _
  obtain ⟨y, hy⟩ := CarnotPoint.exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  have ha : 0 < a := div_pos
    ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (by simpa using hz))
    (by linarith)
  have hclosure : closure D ⊆ horizontalBall (G.horizontalFields hq) x r :=
    CarnotPoint.closure_horizontalBall_boundaryRadius_subset G hq hqpos hspan
      hcompl hz (by linarith) hκ
  have hgc : ContinuousOn g (horizontalBall (G.horizontalFields hq) x r) :=
    continuousOn_horizontalGradientNorm (fun i => (G.horizontalFields_contDiff hq i).continuous)
      (isOpen_horizontalBall G hq hqpos hspan x r) hu
  have hpow : IntegrableOn (fun w => g w ^ p) D :=
    (((Real.continuous_rpow_const hp0.le).comp_continuousOn
      (hgc.mono hclosure)).integrableOn_compact
        (isCompact_closure_horizontalBall G hq hqpos hspan hw z (by positivity))).mono_set subset_closure
  have hI : I ≠ ⊤ := by
    change (∫⁻ w in D, ENNReal.ofReal (g w ^ p)) ≠ ⊤
    rw [← ofReal_integral_eq_lintegral_ofReal hpow
      (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (hgn w) p)]
    exact ENNReal.ofReal_ne_top
  have hA0 : volume A ≠ 0 := (volume_horizontalBall_pos G hq hqpos hspan z ha).ne'
  have hAtop : volume A ≠ ⊤ := (volume_horizontalBall_lt_top G hq hqpos hspan hw z ha.le).ne
  obtain ⟨h, he, henergy, hroot⟩ := exists_normalized_power_energy hI hA0 hAtop hp0
  have hg : AEStronglyMeasurable g (volume.restrict D) :=
    (hgc.mono (subset_closure.trans hclosure)).aestronglyMeasurable
      (isOpen_horizontalBall G hq hqpos hspan z (80 * a)).measurableSet
  have hnorm : eLpNorm g (ENNReal.ofReal p) (volume.restrict D) = I ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hg, ENNReal.toReal_ofReal hp0.le]
    simp_rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hgn _),
      ENNReal.ofReal_rpow_of_nonneg (hgn _) hp0.le]
    rfl
  refine ⟨h, he, ?_, ?_⟩
  · simpa only [ENNReal.coe_rpow_of_nonneg h hp0.le] using henergy
  · have hh := eLpNorm_weak_horizontalPoincare_on_boundaryBall G hq hqpos hspan hw hr hκ hz hp u hu
    dsimp only at hh
    rw [hnorm, hroot] at hh
    simpa only [mul_assoc] using hh

end HeatKernel
