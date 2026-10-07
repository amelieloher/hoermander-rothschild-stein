-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityStrong
public import RothschildStein.G1.LocalStep
public import RothschildStein.P1.HolderChartContinuity

/-!
# Local regularity assembly: lifted charts from the Hörmander rank condition

The lifting theorem statements need a weighted step `s ≥ 2` with `StepSpansAt w s X x₀`. For fields
smooth on an open `Ω` with `bracketSpansOn Ω X` this step exists locally and uniformly on compact
sets (`exists_stepSpansAt_of_compact`, from `G1.exists_uniform_step_buffer`). With it, the lifting theorem
statements give lifted charts at every point (`exists_liftedChart_drift/_noDrift`) and finite
intrinsic Hölder norms give Euclidean continuity (`continuousOn_of_holderENorm_charts`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

variable {n : ℕ}

/-- The weighted step of the Hörmander rank condition is uniform on compact sets: if the fields are
smooth on an open `Ω` and `bracketSpansOn Ω X`, a compact `K ⊆ Ω` has a step `s ≥ 2` with
`StepSpansAt w s X x` for every `x ∈ K`. -/
theorem exists_stepSpansAt_of_compact {k : ℕ} {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (w : Fin k → ℕ+)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X) :
    ∃ s : ℕ, 2 ≤ s ∧ ∀ x ∈ K, StepSpansAt w s X x := by
  obtain ⟨V, -, hKV, -, -, -, s, -, hstep⟩ :=
    RothschildStein.G1.exists_uniform_step_buffer hΩ hK hKΩ w X hX hrank
  refine ⟨max s 2, le_max_right _ _, fun x hx => ?_⟩
  have h := hstep x (subset_closure (hKV hx))
  unfold StepSpansAt
  apply top_unique
  rw [← h]
  apply Submodule.span_mono
  rintro v ⟨I, hI, hw, rfl⟩
  exact ⟨I, hI, hw.trans (le_max_left _ _), rfl⟩

section Charts

variable {q : ℕ}

/-- The lifting theorem statement (drift) gives a lifted chart at a point with a weighted step. -/
theorem exists_liftedChart_drift (R : LiftApproximationDriftStatement) (hn : 0 < n) (hq : 0 < q)
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) {s : ℕ} (hs : 2 ≤ s)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ (Ω : Set (Fin n → ℝ))) (hstep : StepSpansAt driftWeight s X x₀) :
    ∃ m, Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m) := by
  obtain ⟨m, -, hm⟩ := P1.liftedChart_of_drift (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ s
    (R hn hq (Ω : Set (Fin n → ℝ)) Ω.isOpen X hX x₀ hx₀ s hs hstep)
  exact ⟨m, hm⟩

/-- The lifting theorem statement (no drift) gives a lifted chart at a point with a weighted step. -/
theorem exists_liftedChart_noDrift (R : LiftApproximationNoDriftStatement) (hn : 0 < n) (hq : 0 < q)
    (Ω : Opens (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) {s : ℕ} (hs : 2 ≤ s)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ (Ω : Set (Fin n → ℝ))) (hstep : StepSpansAt noDriftWeight s X x₀) :
    ∃ m, Nonempty (P1.LiftedChart noDriftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m) := by
  obtain ⟨m, -, hm⟩ := P1.liftedChart_of_noDrift (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ s
    (R hn hq (Ω : Set (Fin n → ℝ)) Ω.isOpen X hX x₀ hx₀ s hs hstep)
  exact ⟨m, hm⟩

/-- Lifted charts (drift) at every point of `Ω`, from the lifting theorem and the rank condition. -/
theorem hchart_drift (R : LiftApproximationDriftStatement) (hn : 0 < n) (hq : 0 < q)
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) :
    ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m) := by
  intro x₀ hx₀
  obtain ⟨s, hs, hstep⟩ := exists_stepSpansAt_of_compact Ω.isOpen isCompact_singleton
    (singleton_subset_iff.2 hx₀) driftWeight X hX hspan
  obtain ⟨m, hm⟩ := exists_liftedChart_drift R hn hq Ω X hX hs hx₀ (hstep x₀ rfl)
  exact ⟨s, m, hm⟩

/-- Lifted charts (no drift) at every point of `Ω`, from the lifting theorem and the rank condition. -/
theorem hchart_noDrift (R : LiftApproximationNoDriftStatement) (hn : 0 < n) (hq : 0 < q)
    (Ω : Opens (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) :
    ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart noDriftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m) := by
  intro x₀ hx₀
  obtain ⟨s, hs, hstep⟩ := exists_stepSpansAt_of_compact Ω.isOpen isCompact_singleton
    (singleton_subset_iff.2 hx₀) noDriftWeight X hX hspan
  obtain ⟨m, hm⟩ := exists_liftedChart_noDrift R hn hq Ω X hX hs hx₀ (hstep x₀ rfl)
  exact ⟨s, m, hm⟩

/-- A uniform step with lifted charts (drift) at every point of a compact `K ⊆ Ω`. -/
theorem exists_uniform_liftedCharts_drift (R : LiftApproximationDriftStatement) (hn : 0 < n) (hq : 0 < q)
    (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKΩ : K ⊆ (Ω : Set (Fin n → ℝ))) :
    ∃ s : ℕ, ∀ x ∈ K, ∃ m,
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x m) := by
  obtain ⟨s, hs, hstep⟩ := exists_stepSpansAt_of_compact Ω.isOpen hK hKΩ driftWeight X hX hspan
  exact ⟨s, fun x hx => exists_liftedChart_drift R hn hq Ω X hX hs (hKΩ hx) (hstep x hx)⟩

end Charts

/-- A function of finite intrinsic Hölder norm on `Ω` is Euclidean continuous on `Ω`, given lifted
charts at every point (a chart's projected neighborhood is an open set on which the control distance
dominates the Euclidean distance of lifts). -/
theorem continuousOn_of_holderENorm_charts {k : ℕ} {w : Fin k → ℕ+} {Ω : Opens (Fin n → ℝ)}
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart w s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : holderENorm (controlDistance (Ω : Set (Fin n → ℝ)) w X) α (Ω : Set (Fin n → ℝ)) f < ⊤) :
    ContinuousOn f (Ω : Set (Fin n → ℝ)) := by
  intro x₀ hx₀
  obtain ⟨s, m, ⟨C⟩⟩ := hchart x₀ hx₀
  have hsurj : Function.Surjective (basePointCLM n m) :=
    fun y => ⟨joinPoint y (0 : Fin m → ℝ), basePoint_joinPoint y 0⟩
  have hopen : IsOpen (basePoint '' C.U) :=
    (basePointCLM n m).isOpenMap hsurj C.U C.isOpen_U
  let S : Opens (Fin n → ℝ) := ⟨(Ω : Set (Fin n → ℝ)) ∩ basePoint '' C.U, Ω.isOpen.inter hopen⟩
  have hSΩ : (S : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) := inter_subset_left
  have hS : (S : Set (Fin n → ℝ)) ⊆ basePoint '' C.U := inter_subset_right
  have hcont := P1.continuousOn_of_holderENorm_liftedChart C S hS hα
    (lt_of_le_of_lt (RothschildStein.S.holderENorm_mono
      (controlDistance (Ω : Set (Fin n → ℝ)) w X) α (Ω : Set (Fin n → ℝ)) f hSΩ) hf)
  have hx₀S : x₀ ∈ (S : Set (Fin n → ℝ)) :=
    ⟨hx₀, joinPoint x₀ (0 : Fin m → ℝ), C.center_mem, basePoint_joinPoint x₀ 0⟩
  exact (hcont.continuousAt (S.isOpen.mem_nhds hx₀S)).continuousWithinAt

end RothschildStein.P2
