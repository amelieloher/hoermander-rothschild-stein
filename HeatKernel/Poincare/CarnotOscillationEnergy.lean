-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotMeetingIntegral
public import HeatKernel.Poincare.CarnotRadialFamilies
public import HeatKernel.Poincare.CarnotWhitneyOverlap
public import HeatKernel.Poincare.WhitneyEnergyFamily
public import HeatKernel.Poincare.CoverChainIntegral
public import HeatKernel.Poincare.ChainCostCoercion
public import HeatKernel.Poincare.SubtypeOverlap

/-! Global same-ball oscillation bounds from Carnot Whitney geometry. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal BigOperators Classical

namespace HeatKernel

/-- A continuously differentiable function inside a horizontal ball has an oscillation
bound about one constant using only the horizontal energy in the same ball. -/
theorem exists_const_lintegral_oscillation_le_horizontal_energy {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r κ p : ℝ} (hr : 0 < r) (hκ : 240 < κ)
    (k : ℕ) (hk : 0 < k) (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 1 u (horizontalBall (G.horizontalFields hq) x r)) :
    ∃ c : ℝ, (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
      ENNReal.ofReal (|u y - c| ^ p)) ≤
      (ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2)) ^ p) *
        ENNReal.ofReal ((5 : ℝ) ^ G.homogeneousDimension)) *
        ENNReal.ofReal ((2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ)) ^ (p - 1)) *
        ENNReal.ofReal ((κ + 13) ^ G.homogeneousDimension) * ENNReal.ofReal r *
        (1000 ^ G.homogeneousDimension : ℕ) *
        ∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
          ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u y ^ p) := by
  classical
  obtain ⟨C, hCU, hcount, hdisj, hcover, hinterior, hover⟩ :=
    CarnotPoint.exists_countable_boundaryBall_cover_with_overlap G hq hqpos hspan hw x hr hκ
  let _ : Countable C := hcount.to_subtype
  let U := horizontalBall (G.horizontalFields hq) x r
  let a := fun z : C => infDist z.val (ball x r)ᶜ / κ
  let A := fun z : C => horizontalBall (G.horizontalFields hq) z.val (a z)
  let V := fun z : C => horizontalBall (G.horizontalFields hq) z.val (5 * a z)
  let D := fun z : C => horizontalBall (G.horizontalFields hq) z.val (80 * a z)
  let c := fun z : C => ⨍ y in horizontalBall (G.horizontalFields hq) z.val (20 * a z), u y
  obtain ⟨y, hy⟩ := CarnotPoint.exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  have hκ0 : 0 < κ := by linarith
  have ha : ∀ z : C, 0 < a z := fun z => div_pos
    ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hCU z.property)) hκ0
  have hx : x ∈ ⋃ z ∈ C, ball z (5 * (infDist z (ball x r)ᶜ / κ)) :=
    hcover ▸ mem_ball_self hr
  obtain ⟨z₀, hz₀, hroot⟩ := mem_iUnion₂.mp hx
  let root : C := ⟨z₀, hz₀⟩
  obtain ⟨γ, chain, hgeom, hshadow⟩ :=
    CarnotPoint.exists_finite_radial_families_with_shadow_bounds G hq hqpos hspan hw C hr
      (by linarith) hCU hdisj k hk hscale
  obtain ⟨h, hcost, hedge⟩ := exists_boundaryBall_energy_family G hq hqpos hspan hw (κ := κ) hr
    (by linarith) C hCU hp u hu
  let w : C → ℝ≥0 := fun z => ⟨a z, (ha z).le⟩
  let rn : ℝ≥0 := ⟨r, hr.le⟩
  let R : ℝ≥0 := ⟨2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ), by positivity⟩
  let H := ENNReal.ofReal ((κ + 13) ^ G.homogeneousDimension)
  let K := ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2)) ^ p) *
    ENNReal.ofReal ((5 : ℝ) ^ G.homogeneousDimension)
  have hDU : ∀ z, D z ⊆ U := by
    intro z
    have hh : ball z.val (80 * a z) ⊆ ball x r := hinterior z.val z.property
    have hi := Set.image_mono (f := CarnotPoint.coordinateHomeomorph G hq hqpos hspan) hh
    rwa [CarnotPoint.coordinateHomeomorph_image_ball G hq hqpos hspan,
      CarnotPoint.coordinateHomeomorph_image_ball G hq hqpos hspan] at hi
  have hVU : ∀ z, V z ⊆ U := by
    intro z
    have hh : ball z.val (5 * a z) ⊆ ball x r :=
      (ball_subset_ball (by linarith [ha z])).trans (hinterior z.val z.property)
    have hi := Set.image_mono (f := CarnotPoint.coordinateHomeomorph G hq hqpos hspan) hh
    rwa [CarnotPoint.coordinateHomeomorph_image_ball G hq hqpos hspan,
      CarnotPoint.coordinateHomeomorph_image_ball G hq hqpos hspan] at hi
  have hVcover : U ⊆ ⋃ z : C, V z := by
    have hh : ball x r = ⋃ z : C, ball z.val (5 * a z) := by
      simpa only [a, Set.iUnion_subtype] using hcover
    simp only [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan] at hh
    exact hh.le
  have hlocal : ∀ z, (∫⁻ y in V z, ENNReal.ofReal (|u y - c root| ^ p)) ≤
      K * (volume (A z) * (((∑ j ∈ chain z, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)) := by
    intro z
    have hf : AEStronglyMeasurable (fun y => u y - c root) (volume.restrict (V z)) :=
      ((hu.continuousOn.mono (hVU z)).sub continuousOn_const).aestronglyMeasurable
        (isOpen_horizontalBall G hq hqpos hspan z.val (5 * a z)).measurableSet
    have hh := lintegral_abs_sub_rpow_le_radial_meeting_cost G hq hqpos hspan hw C hr
      (by linarith) hCU hcover z root hroot a c (fun _ => rfl) h hp u
      (fun j => (hcost j).2.2) hedge (hgeom z).1 (hgeom z).2.1 (hgeom z).2.2.1
      (chain z) (hgeom z).2.2.2.1 hf
    have heq : ENNReal.ofReal ((∑ j ∈ chain z, a j * (h j : ℝ)) ^ p) =
        (((∑ j ∈ chain z, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞) :=
      ofReal_sum_mul_rpow_eq_coe (chain z) w h p
    rw [heq] at hh
    exact hh.trans_eq (by dsimp only [K, A]; ac_rfl)
  have hradius : ∀ z, ∑ j ∈ chain z, w j ≤ R := by
    intro z
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sum]
    change (∑ j ∈ chain z, a j) ≤ 2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ)
    exact (hgeom z).2.2.2.2
  have hmax : ∀ z, w z ≤ rn := by
    intro z
    have hb := div_le_div_of_nonneg_right
      (infDist_ball_compl_le_two_mul (hCU z.property) hy) hκ0.le
    have hdiv : 2 * r / κ ≤ r := (div_le_iff₀ hκ0).mpr (by nlinarith)
    exact hb.trans hdiv
  have hshadow' : ∀ j, (∑' z : {z : C | j ∈ chain z}, volume (A z.val)) ≤ H * volume (A j) := by
    intro j
    have hh := hshadow j
    change (∑' z : {z : C | j ∈ chain z}, CarnotPoint.volume G hq hqpos hspan
      (ball z.val.val (a z.val))) ≤ H * CarnotPoint.volume G hq hqpos hspan (ball j.val (a j)) at hh
    have hm : ∀ z : C, CarnotPoint.volume G hq hqpos hspan (ball z.val (a z)) = volume (A z) := by
      intro z
      rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
      rfl
    simp_rw [hm] at hh
    exact hh
  have hov : ∀ y : Fin N → ℝ, {j : C | y ∈ D j}.Finite ∧
      {j : C | y ∈ D j}.ncard ≤ 1000 ^ G.homogeneousDimension := by
    intro y
    have hh := finite_ncard_subtype_overlap C
      (fun z => ball z (80 * (infDist z (ball x r)ᶜ / κ)))
      (show CarnotPoint G hq hqpos hspan from y) (1000 ^ G.homogeneousDimension)
      (hover y).1 (hover y).2
    have heq : ∀ j : C, (show CarnotPoint G hq hqpos hspan from y) ∈
        ball j.val (80 * a j) ↔ y ∈ D j := by
      intro j
      rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
      rfl
    have hset : {j : C | (show CarnotPoint G hq hqpos hspan from y) ∈
        ball j.val (80 * a j)} = {j : C | y ∈ D j} := Set.ext fun j => heq j
    rw [hset] at hh
    exact hh
  have hg : AEMeasurable (fun y => ENNReal.ofReal
      (horizontalGradientNorm (G.horizontalFields hq) u y ^ p)) (volume.restrict U) :=
    (((Real.continuous_rpow_const (le_trans zero_le_one hp)).comp_continuousOn
      (continuousOn_horizontalGradientNorm (fun i => (G.horizontalFields_contDiff hq i).continuous)
        (isOpen_horizontalBall G hq hqpos hspan x r) hu)).aestronglyMeasurable
          (isOpen_horizontalBall G hq hqpos hspan x r).measurableSet).aemeasurable.ennreal_ofReal
  have hh := setLIntegral_le_energy_of_cover_chain_bounds volume U V D hVcover
    (fun j => (isOpen_horizontalBall G hq hqpos hspan j.val (80 * a j)).measurableSet) hDU
    (fun y => ENNReal.ofReal (|u y - c root| ^ p))
    (fun y => ENNReal.ofReal (horizontalGradientNorm (G.horizontalFields hq) u y ^ p)) hg
    chain (fun z => volume (A z)) (fun z => volume (A z)) w h hp R rn H K
    (1000 ^ G.homogeneousDimension) hlocal hradius hmax hshadow'
    (fun j => (hcost j).2.1.le) (fun y => (hov y).1) (fun y => (hov y).2)
  refine ⟨c root, ?_⟩
  have hR : ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal ((2 * (k ^ G.homogeneousDimension : ℕ) * (2 * r / κ)) ^ (p - 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow]
    rfl
  have hrn : (rn : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  simpa only [hR, hrn, H, K, U] using hh

end HeatKernel
