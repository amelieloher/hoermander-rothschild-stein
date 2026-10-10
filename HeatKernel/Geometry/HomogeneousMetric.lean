-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalMetric
public import HeatKernel.Geometry.FiniteBracketStep
public import HeatKernel.Geometry.BallCovariance
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff

/-! The horizontal metric and compact closed balls on a homogeneous group. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped NNReal ENNReal
namespace HeatKernel

/-- The horizontal fields of a bracket-generating homogeneous group have a positive
finite bracket step. -/
theorem exists_positive_bracketStepOn_horizontalFields {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    ∃ s, 1 ≤ s ∧ bracketStepOn univ (fun _ : Fin q => 1) (G.horizontalFields hq) s := by
  obtain ⟨s, hs⟩ := exists_bracketStepOn_horizontalFields G hq hspan
  refine ⟨max 1 s, le_max_left _ _, fun x hx => ?_⟩
  apply top_unique
  rw [← hs x hx]
  apply Submodule.span_mono
  rintro v ⟨I, hI, hW, hv⟩
  exact ⟨I, hI, hW.trans (le_max_right _ _), hv⟩

/-- A bracket-generating homogeneous group carries its finite horizontal metric with
Euclidean coordinate topology. -/
@[instance_reducible]
def homogeneousHorizontalMetricSpace {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq)) : MetricSpace (Fin N → ℝ) :=
  let hs := (exists_positive_bracketStepOn_horizontalFields G hq hspan).choose_spec
  horizontalMetricSpace hqpos (G.horizontalFields hq) (G.horizontalFields_contDiff hq) hs.1 hs.2

/-- The horizontal distance of a bracket-generating homogeneous group is jointly
continuous in coordinate space. -/
theorem continuous_homogeneous_horizontalL2Distance {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      horizontalL2Distance (G.horizontalFields hq) p.1 p.2) := by
  obtain ⟨s, hs, hstep⟩ := exists_positive_bracketStepOn_horizontalFields G hq hspan
  exact continuous_horizontalL2Distance hqpos _ (G.horizontalFields_contDiff hq) hs hstep

/-- Closed horizontal balls of finite radius are compact in coordinate space. -/
theorem isCompact_horizontal_closedBall {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) (x : Fin N → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact {y | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal R} := by
  obtain ⟨ε, hε, hbound⟩ := RothschildStein.G1.exists_controlBall_subset_euclideanBall
    isOpen_univ (fun _ : Fin q => 1) (G.horizontalFields hq)
    (fun i => (G.horizontalFields_contDiff hq i).continuous.continuousOn)
    (mem_univ (0 : Fin N → ℝ)) (by norm_num : (0 : ℝ) < 1)
  let r := ε / (R + 1)
  have hr : 0 < r := div_pos hε (by linarith)
  have hrR : r * R < ε := by
    dsimp [r]
    have hh : ε / (R + 1) * (R + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  let F := fun z : Fin N → ℝ => G.mul x (G.dilate r⁻¹ z)
  have hF : Continuous F := (G2.contDiff_leftTranslation G x).continuous.comp
    (G2.contDiff_dilate G r⁻¹).continuous
  have hcompact : IsCompact (F '' Metric.closedBall (0 : Fin N → ℝ) 1) :=
    (isCompact_closedBall (0 : Fin N → ℝ) 1).image hF
  have hclosed : IsClosed {y | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal R} :=
    isClosed_le ((continuous_homogeneous_horizontalL2Distance G hq hqpos hspan).comp
      (continuous_const.prodMk continuous_id)) continuous_const
  apply hcompact.of_isClosed_subset hclosed
  intro y hy
  let z := G.mul (G.inv x) y
  have hzy : horizontalL2Distance (G.horizontalFields hq) 0 z =
      horizontalL2Distance (G.horizontalFields hq) x y := by
    simpa only [G2.inv_mul] using horizontalL2Distance_leftTranslation G hq (G.inv x) x y
  have hscaled : horizontalL2Distance (G.horizontalFields hq) 0 (G.dilate r z) < ENNReal.ofReal ε := by
    have he := horizontalL2Distance_dilate G hq hw hr (0 : Fin N → ℝ) z
    rw [G2.dilate_zero, hzy] at he
    rw [he]
    apply (mul_le_mul le_rfl hy bot_le bot_le).trans_lt
    rw [← ENNReal.ofReal_mul hr.le]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hrR
  have hn := hbound (G.dilate r z)
    ((controlDistance_le_horizontalL2Distance (G.horizontalFields hq) 0 (G.dilate r z)).trans_lt hscaled)
  refine ⟨G.dilate r z, hn.le, ?_⟩
  dsimp [F]
  rw [G2.dilate_inv_dilate G hr.ne']
  dsimp [z]
  rw [← G2.mul_assoc, G2.mul_inv, G2.zero_mul]

end HeatKernel
