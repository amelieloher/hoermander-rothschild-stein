-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingNoDriftSolve
public import RothschildStein.P2.SmoothingGlue

/-!
# Distributional smoothing without drift: local representatives on cylinders

The no-drift counterpart of the `LocalDescent` section of `SmoothingGlue`. In a lifted no-drift
chart `C` centred at `x₀` (alphabet `Fin q`, weights one, `L = ∑ Xᵢ²`):

* `exists_cylinder_descent_data_noDrift`: a cylinder `A × B` around the lift of `x₀` with compact
  closure in the solve-subtract ball, and the normalized test `η`;
* `exists_local_representative_sobolev_noDrift_of_localSolvability`: `T|_A` is represented by
  `u ∈ W^{2,p}_X(A)` (lift, solve, subtract, descend on the cylinder);
* `exists_local_representative_holder_noDrift_of_localSolvability`: `T|_A` is represented by a
  continuous `u` all of whose words of weight at most two are continuous weak derivatives on `A`.

The descent lemmas (`memSobolevX_descent`, `hasWeakWordDeriv_descent_continuous`) and the chart
fiber setting of a cylinder are alphabet-generic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section LocalDescentNoDrift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The cylinder data used by the descent at the centre of a no-drift chart: a cylinder `A × B`
inside the open set `UR ⊆ U` whose closure is compact in `UR`, the test `η`, and the inclusion
`A ≤ Ω`. -/
theorem exists_cylinder_descent_data_noDrift {UR : Opens (Fin (n + m) → ℝ)}
    (hξUR : joinPoint x₀ (0 : Fin m → ℝ) ∈ (UR : Set (Fin (n + m) → ℝ)))
    (hURU : (UR : Set (Fin (n + m) → ℝ)) ⊆ C.U) :
    ∃ (A : Opens (Fin n → ℝ)) (B : Opens (Fin m → ℝ)) (η : TestFunction B ℝ (⊤ : ℕ∞)),
      x₀ ∈ (A : Set (Fin n → ℝ)) ∧ (0 : Fin m → ℝ) ∈ (B : Set (Fin m → ℝ)) ∧
      IsCompact (closure (cylinder A B : Set (Fin (n + m) → ℝ))) ∧
      closure (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ (UR : Set (Fin (n + m) → ℝ)) ∧
      volume (B : Set (Fin m → ℝ)) < ⊤ ∧ 0 < volume (B : Set (Fin m → ℝ)) ∧
      (∫ t : Fin m → ℝ, η t = 1) ∧ (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U ∧
      A ≤ liftedChartBaseOpens C := by
  obtain ⟨A, B, hxA, h0B, hcpt, hcl, hBfin, hBpos⟩ := exists_cylinder_closure_subset hξUR
  obtain ⟨η, hη⟩ := exists_test_integral_eq_one B h0B
  have hsubU : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    (subset_closure.trans hcl).trans hURU
  refine ⟨A, B, η, hxA, h0B, hcpt, hcl, hBfin, hBpos, hη, hsubU, fun x hx => ?_⟩
  have h1 : joinPoint x (0 : Fin m → ℝ) ∈ (cylinder A B : Set (Fin (n + m) → ℝ)) :=
    joinPoint_mem_cylinder.2 ⟨hx, h0B⟩
  have := liftedChart_basePoint_mem C (hsubU h1)
  rwa [basePoint_joinPoint] at this

/-- **Local representative, Sobolev case, no drift, under a `LocalSolvabilityNoDrift` hypothesis.** In a lifted no-drift chart `C` centred at `x₀`, let `T ∈ 𝒟'(Ω)` with `L T = f`,
`L = ∑ Xᵢ²`, `f ∈ L^p(Ω)`, `1 < p < ∞`. Then there is an open `A ∋ x₀`, `A ⊆ Ω`, and a function `u`
representing `T|_A` with `u ∈ W^{2,p}_X(A)` (`memSobolevX`): lift, solve (local solvability), subtract and
descend (`memSobolevX_descent`), on a cylinder `A × B` around the lift of `x₀` (BB pp. 608-610). -/
theorem exists_local_representative_sobolev_noDrift_of_localSolvability
    (hP : LocalSolvabilityNoDrift C) {p : ℝ≥0∞} (hp : 1 < p) (hpt : p < ⊤)
    (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞))
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p (volume.restrict Ω))
    (hT : hasDistributionEquation (liftedChartBaseOpens C) X (liftedChart_contDiffOn_base C) T f) :
    ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ liftedChartBaseOpens C ∧
      ∃ u : (Fin n → ℝ) → ℝ,
        representsDistribution A
          (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T) u ∧
        memSobolevX noDriftWeight X A 2 p u := by
  obtain ⟨UR, hξUR, hURU, w, hwloc, hrepr, hSob⟩ :=
    solve_subtract_sobolev_noDrift_of_localSolvability C hP hp hpt T hf hT C.center_mem
  obtain ⟨A, B, η, hxA, h0B, hcpt, hcl, hBfin, hBpos, hη, hsubU, hA⟩ :=
    exists_cylinder_descent_data_noDrift C hξUR hURU
  have hsub : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ UR := subset_closure.trans hcl
  let S := liftedChart_cylinderFiberSetting C A B hsubU hBfin
  have hS : memSobolevX noDriftWeight C.Xl (cylinder A B) 2 p w := hSob (cylinder A B) hcpt hcl
  have hrepr_cyl : RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) (cylinder A B)
      (liftedChartLift C T) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) := by
    rw [← distributionRestriction_restriction (liftedChartOpens C) UR (cylinder A B) hsub hURU,
      hrepr, distributionRestriction_ofFun UR (cylinder A B) hsub hwloc]
  have hT_cyl := (liftedChartFiberIntegration C).restrict_lift_ofFun hsubU hA S T hrepr_cyl
  obtain ⟨hrep, -, hmem⟩ := memSobolevX_descent noDriftWeight X C.P
    (fun i => (liftedChart_contDiffOn_lift C i).mono hsubU)
    (fun i => (liftedChart_contDiffOn_base C i).mono hA) S hη
    (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T) hT_cyl hp.le hpt.ne
    hBpos hBfin hS
  exact ⟨A, hxA, hA, fiberAvg w η, hrep, hmem⟩

/-- **Local representative, Hölder case, no
drift, under a `LocalSolvabilityNoDrift` hypothesis.** In a lifted no-drift chart `C` centred at `x₀`, let `T ∈ 𝒟'(Ω)` with
`L T = f`, `L = ∑ Xᵢ²`, `f ∈ C^α_X(Ω)`, `0 < α < 1`. Then there is an open `A ∋ x₀`, `A ⊆ Ω`, and a
continuous function `u` representing `T|_A`, every word derivative `X_I u`, `I` of weight at most
two, of which exists as a continuous weak derivative on `A` (so is the intrinsic derivative,
`hasIntrinsicWordDeriv_of_continuous_weak_words`). -/
theorem exists_local_representative_holder_noDrift_of_localSolvability
    (hP : LocalSolvabilityNoDrift C) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞)) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX noDriftWeight X (controlDistance Ω noDriftWeight X) (liftedChartBaseOpens C) 0 α f)
    (hT : hasDistributionEquation (liftedChartBaseOpens C) X (liftedChart_contDiffOn_base C) T f) :
    ∃ A : Opens (Fin n → ℝ), x₀ ∈ (A : Set (Fin n → ℝ)) ∧ A ≤ liftedChartBaseOpens C ∧
      ∃ u : (Fin n → ℝ) → ℝ,
        representsDistribution A
          (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T) u ∧
        ContinuousOn u (A : Set (Fin n → ℝ)) ∧
        ∀ I ∈ wordFamily noDriftWeight 2, ∃ g : (Fin n → ℝ) → ℝ,
          hasWeakWordDeriv X A I u g ∧ ContinuousOn g (A : Set (Fin n → ℝ)) := by
  obtain ⟨UR, hξUR, hURU, w, hwc, hrepr, hSob⟩ :=
    solve_subtract_holder_noDrift_of_localSolvability C hP hα hα1 T hf hT C.center_mem
  obtain ⟨A, B, η, hxA, h0B, hcpt, hcl, hBfin, hBpos, hη, hsubU, hA⟩ :=
    exists_cylinder_descent_data_noDrift C hξUR hURU
  have hsub : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ UR := subset_closure.trans hcl
  let S := liftedChart_cylinderFiberSetting C A B hsubU hBfin
  have hS : memHolderX noDriftWeight C.Xl C.dl (cylinder A B) 2 α w := hSob (cylinder A B) hcpt hcl
  have hwc' : ContinuousOn w (cylinder A B : Set (Fin (n + m) → ℝ)) := hwc.mono hsub
  have hwloc : LocallyIntegrableOn w (UR : Set (Fin (n + m) → ℝ)) volume :=
    hwc.locallyIntegrableOn UR.isOpen.measurableSet
  have hrepr_cyl : RothschildStein.S.distributionRestrictionCLM (liftedChartOpens C) (cylinder A B)
      (liftedChartLift C T) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) := by
    rw [← distributionRestriction_restriction (liftedChartOpens C) UR (cylinder A B) hsub hURU,
      hrepr, distributionRestriction_ofFun UR (cylinder A B) hsub hwloc]
  have hT_cyl := (liftedChartFiberIntegration C).restrict_lift_ofFun hsubU hA S T hrepr_cyl
  obtain ⟨jet, hj0, hjet⟩ := exists_jets_of_memHolderX C hα hsubU hS
  have hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X C.P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)) := fun i =>
    (liftedChart_contDiffOn_lift C i).mono hsubU
  have hXb : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)) := fun i =>
    (liftedChart_contDiffOn_base C i).mono hA
  have hdesc : ∀ I ∈ wordFamily noDriftWeight 2,
      ContinuousOn (fun x => w (joinPoint x (0 : Fin m → ℝ))) (A : Set (Fin n → ℝ)) ∧
      ContinuousOn (fun x => jet I (joinPoint x (0 : Fin m → ℝ))) (A : Set (Fin n → ℝ)) ∧
      representsDistribution A
        (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T)
        (fun x => w (joinPoint x (0 : Fin m → ℝ))) ∧
      hasWeakWordDeriv X A I (fun x => w (joinPoint x (0 : Fin m → ℝ)))
        (fun x => jet I (joinPoint x (0 : Fin m → ℝ))) := by
    intro I hI
    obtain ⟨-, hweak, hcont, -⟩ := hjet I hI
    obtain ⟨h1, h2, h3, h4, -⟩ := hasWeakWordDeriv_descent_continuous X C.P hXt hXb S hη
      (RothschildStein.S.distributionRestrictionCLM (liftedChartBaseOpens C) A T)
      (hwc'.locallyIntegrableOn (cylinder A B).isOpen.measurableSet) hT_cyl I hweak hwc' hcont h0B
    exact ⟨h1, h2, h3, h4⟩
  have h00 := hdesc [] (RothschildStein.S.nil_mem_wordFamily noDriftWeight 2)
  exact ⟨A, hxA, hA, fun x => w (joinPoint x (0 : Fin m → ℝ)), h00.2.2.1, h00.1,
    fun I hI => ⟨fun x => jet I (joinPoint x (0 : Fin m → ℝ)), (hdesc I hI).2.2.2,
      (hdesc I hI).2.1⟩⟩

end LocalDescentNoDrift

end RothschildStein.P2
