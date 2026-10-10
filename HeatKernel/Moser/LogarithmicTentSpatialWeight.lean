-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicSquaredSpatialWeight
public import HeatKernel.Moser.LogarithmicTentGradient
public import HeatKernel.Sobolev.TentVolume
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Literal squared distance tents as logarithmic spatial weights -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
namespace HeatKernel

/-- The distance tent is continuous and has compact support inside every strictly
larger horizontal ball. -/
theorem logarithmic_tent_continuous_compact_support {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0
    Continuous η ∧ HasCompactSupport η ∧
      tsupport η ⊆ horizontalBall (G.horizontalFields hq) x R := by
  let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0
  have hfinite (y : Fin N → ℝ) : horizontalL2Distance (G.horizontalFields hq) x y ≠ ⊤ :=
    horizontalL2Distance_ne_top_of_bracketSpansOn hqpos _ (G.horizontalFields_contDiff hq) hspan x y
  have hd : Continuous (fun y => horizontalL2Distance (G.horizontalFields hq) x y) :=
    (continuous_homogeneous_horizontalL2Distance G hq hqpos hspan).comp
      (continuous_const.prodMk continuous_id)
  have hreal : Continuous (fun y => (horizontalL2Distance (G.horizontalFields hq) x y).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (hfinite y)).comp hd.continuousAt
  have hclosed : tsupport η ⊆
      {y | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal r} := by
    apply closure_minimal _ (isClosed_le hd continuous_const)
    intro y hy
    rw [mem_ofPred_eq, ← ENNReal.toReal_le_toReal (hfinite y) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr.le]
    apply le_of_not_gt
    intro hlt
    have hdiv : 1 ≤ (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r :=
      (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hlt.le)
    exact hy (max_eq_right (by linarith))
  refine ⟨(continuous_const.sub (hreal.div_const r)).max continuous_const,
    (isCompact_horizontal_closedBall G hq hqpos hspan hw x hr.le).of_isClosed_subset
      (isClosed_tsupport _) hclosed, ?_⟩
  intro y hy
  exact (hclosed hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrR)).mpr hrR)

/-- The literal squared tent has a spatial multiplier and fixed test with gradient
exactly twice the tent times its sharp square-integrable cutoff gradient. -/
theorem exists_logarithmic_tent_spatial_weight {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    let V : Opens (Fin N → ℝ) :=
      ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
    let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0
    ∃ e : energyGraph (N := N) ⊤ (G.horizontalFields hq),
      ∃ W : WeakSolutionSpatialWeight V (G.horizontalFields hq),
      ∃ w : zeroBoundaryGraph V (G.horizontalFields hq),
      (e : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] η ∧
      (∀ᵐ y ∂volume, ∑ i, ((e : GradientSpace (N := N) ⊤ q).snd i y) ^ 2 ≤ (r ^ 2)⁻¹) ∧
      W.toFun = (fun y => η y ^ 2) ∧
      W.gradient = (fun i y => 2 * η y * (e : GradientSpace (N := N) ⊤ q).snd i y) ∧
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun ∧
      (∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i) ∧
      (0 < ∫ y, W.toFun y) ∧
      ∀ᵐ y ∂volume, y ∉ horizontalBall (G.horizontalFields hq) x r →
        ∀ i, (e : GradientSpace (N := N) ⊤ q).snd i y = 0 := by
  let V : Opens (Fin N → ℝ) :=
    ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
  let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / r) 0
  obtain ⟨e, hv, hg, hzero⟩ := exists_logarithmic_tent_energy_gradient G hq hqpos hspan hw x hr
  obtain ⟨hcont, hc, hs⟩ := logarithmic_tent_continuous_compact_support G hq hqpos hspan hw x hr hrR
  have hη : ∀ y, 0 ≤ η y ∧ η y ≤ 1 := by
    intro y
    refine ⟨le_max_right _ _, max_le ?_ (by norm_num)⟩
    have hnonneg := ENNReal.toReal_nonneg (a := horizontalL2Distance (G.horizontalFields hq) x y)
    have := div_nonneg hnonneg hr.le
    linarith
  have hb : ∀ᵐ y ∂volume, ‖η y‖ ≤ 1 := Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hη y).1]
    exact (hη y).2
  have hd (i : Fin q) : ∀ᵐ y ∂volume, ‖(e : GradientSpace (N := N) ⊤ q).snd i y‖ ≤ r⁻¹ := by
    filter_upwards [hg] with y hy
    have hi : ((e : GradientSpace (N := N) ⊤ q).snd i y) ^ 2 ≤
        ∑ j, ((e : GradientSpace (N := N) ⊤ q).snd j y) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((e : GradientSpace (N := N) ⊤ q).snd j y) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hsq := hi.trans hy
    rw [← inv_pow] at hsq
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs ((e : GradientSpace (N := N) ⊤ q).snd i y),
      abs_nonneg ((e : GradientSpace (N := N) ⊤ q).snd i y), inv_nonneg.mpr hr.le]
  obtain ⟨W, w, hW, hD, hwv, hwd⟩ := exists_squared_logarithmic_spatial_weight V
    (G.horizontalFields hq) (G.horizontalFields_contDiff hq) e hcont hc hs hv hb
    (inv_nonneg.mpr hr.le) hd
  refine ⟨e, W, w, hv, hg, hW, hD, hwv, hwd, ?_, hzero⟩
  rw [hW]
  exact Sobolev.integral_horizontal_tent_sq_pos G hq hqpos hspan hw x hr

end HeatKernel
