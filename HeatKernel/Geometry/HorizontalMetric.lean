-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.ControlComparison
public import HeatKernel.Geometry.HorizontalTriangle

/-! Separation and the Euclidean topology of the horizontal control metric. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein RothschildStein.G1
open scoped NNReal ENNReal Topology
namespace HeatKernel

/-- Continuous horizontal fields give separation for their length distance. -/
theorem horizontalL2Distance_eq_zero_iff {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, Continuous (X i))
    (x y : Fin N → ℝ) : horizontalL2Distance X x y = 0 ↔ x = y := by
  refine ⟨fun hd => ?_, fun he => by subst y; exact horizontalL2Distance_self X x⟩
  apply (controlDistance_eq_zero_iff isOpen_univ (fun _ => 1) X
    (fun i => (hX i).continuousOn) (mem_univ x)).1
  apply le_antisymm _ bot_le
  simpa [hd] using controlDistance_le_horizontalL2Distance X x y

/-- The horizontal length distance defines an extended metric for continuous fields. -/
@[instance_reducible]
def horizontalEMetricSpace {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, Continuous (X i)) :
    EMetricSpace (Fin N → ℝ) :=
  { PseudoEMetricSpace.ofEDist (horizontalL2Distance X)
      (horizontalL2Distance_self X) (horizontalL2Distance_comm X) (horizontalL2Distance_triangle X) with
    eq_of_edist_eq_zero := fun h => (horizontalL2Distance_eq_zero_iff X hX _ _).1 h }

/-- Local control comparison places a Euclidean neighborhood inside every positive
horizontal ball. -/
theorem exists_euclideanBall_subset_horizontalBall {N q s : ℕ} (hq : 0 < q)
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (hs : 0 < s)
    (hcmp : LocalControlComparison univ (fun _ : Fin q => 1) X s)
    (x : Fin N → ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ y, dist y x < r → horizontalL2Distance X x y < ε := by
  let C := ENNReal.ofReal (Real.sqrt q)
  have hC : C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 (Nat.cast_pos.2 hq)))
  have hCf : C ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨r, hr, hsub⟩ := exists_euclideanBall_subset_controlBall_of_local_comparison hs hcmp
    (mem_univ x) (ENNReal.div_pos hε.ne' hCf : 0 < ε / C)
  refine ⟨r, hr, fun y hy => ?_⟩
  apply (horizontalL2Distance_le_sqrt_mul_controlDistance hq X x y).trans_lt
  exact (ENNReal.mul_right_strictMono hC hCf (hsub y (mem_univ y) hy)).trans_eq
    (ENNReal.mul_div_cancel hC hCf)

/-- The extended horizontal metric has exactly the Euclidean coordinate topology
whenever the componentwise local comparison holds. -/
theorem horizontalEMetricSpace_topology_eq_of_local_comparison {N q s : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, Continuous (X i))
    (hs : 0 < s) (hcmp : LocalControlComparison univ (fun _ : Fin q => 1) X s) :
    (horizontalEMetricSpace X hX).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Fin N → ℝ)) := by
  apply TopologicalSpace.ext
  funext U
  apply propext
  constructor
  · intro hU
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨ε, hε, hsub⟩ :=
      (@EMetric.isOpen_iff (Fin N → ℝ) U (horizontalEMetricSpace X hX).toPseudoEMetricSpace).mp hU x hx
    obtain ⟨r, hr, hrsub⟩ := exists_euclideanBall_subset_horizontalBall hq hs hcmp x hε
    refine ⟨r, hr, fun y hy => hsub ?_⟩
    change horizontalL2Distance X y x < ε
    rw [horizontalL2Distance_comm X y x]
    exact hrsub y hy
  · intro hU
    apply (@EMetric.isOpen_iff (Fin N → ℝ) U (horizontalEMetricSpace X hX).toPseudoEMetricSpace).mpr
    intro x hx
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨ε, hε, hεsub⟩ := exists_controlBall_subset_euclideanBall isOpen_univ (fun _ => 1) X
      (fun i => (hX i).continuousOn) (mem_univ x) hr
    refine ⟨ENNReal.ofReal ε, ENNReal.ofReal_pos.mpr hε, fun y hy => hsub ?_⟩
    apply hεsub y
    apply (controlDistance_le_horizontalL2Distance X x y).trans_lt
    change horizontalL2Distance X y x < ENNReal.ofReal ε at hy
    simpa only [horizontalL2Distance_comm X y x] using hy

/-- Smooth finite-step fields have the Euclidean topology for their horizontal metric. -/
theorem horizontalEMetricSpace_topology_eq_of_bracketStepOn {N q s : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hs : 1 ≤ s) (hstep : bracketStepOn univ (fun _ : Fin q => 1) X s) :
    (horizontalEMetricSpace X (fun i => (hX i).continuous)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Fin N → ℝ)) := by
  apply horizontalEMetricSpace_topology_eq_of_local_comparison hq X (fun i => (hX i).continuous)
    (Nat.zero_lt_of_lt hs)
  exact localControlComparison_of_smooth_bracketStep isOpen_univ (fun _ => 1) X
    (fun i => (hX i).contDiffOn) hs (fun _ => hs) hstep

/-- A finite bracket step implies the unrestricted bracket-spanning condition. -/
theorem bracketSpansOn_of_bracketStepOn {N q s : ℕ}
    {Ω : Set (Fin N → ℝ)} {w : Fin q → ℕ+}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (h : bracketStepOn Ω w X s) :
    bracketSpansOn Ω X := by
  intro x hx
  apply top_unique
  rw [← h x hx]
  apply Submodule.span_mono
  rintro v ⟨I, hI, _, hv⟩
  exact ⟨I, hI, hv⟩

/-- The horizontal extended metric with definitionally Euclidean coordinate topology. -/
@[instance_reducible]
def horizontalEuclideanEMetricSpace {N q s : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hs : 1 ≤ s) (hstep : bracketStepOn univ (fun _ : Fin q => 1) X s) :
    EMetricSpace (Fin N → ℝ) :=
  (horizontalEMetricSpace X (fun i => (hX i).continuous)).replaceTopology
    (horizontalEMetricSpace_topology_eq_of_bracketStepOn hq X hX hs hstep).symm

/-- The horizontal distance is jointly continuous in Euclidean coordinates. -/
theorem continuous_horizontalL2Distance {N q s : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hs : 1 ≤ s) (hstep : bracketStepOn univ (fun _ : Fin q => 1) X s) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => horizontalL2Distance X p.1 p.2) := by
  exact @continuous_edist (Fin N → ℝ) (horizontalEuclideanEMetricSpace hq X hX hs hstep).toPseudoEMetricSpace

/-- Smooth finite-step fields define a finite horizontal metric with the Euclidean topology. -/
@[instance_reducible]
def horizontalMetricSpace {N q s : ℕ} (hq : 0 < q)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hs : 1 ≤ s) (hstep : bracketStepOn univ (fun _ : Fin q => 1) X s) :
    MetricSpace (Fin N → ℝ) := by
  letI := horizontalEuclideanEMetricSpace hq X hX hs hstep
  exact EMetricSpace.toMetricSpace (fun x y =>
    horizontalL2Distance_ne_top_of_bracketSpansOn hq X hX (bracketSpansOn_of_bracketStepOn hstep) x y)

end HeatKernel
