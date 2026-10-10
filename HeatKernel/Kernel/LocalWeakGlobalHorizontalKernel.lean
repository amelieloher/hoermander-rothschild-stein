-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ConservativeGlobalHorizontalKernel
public import HeatKernel.Kernel.JointKernelLocalWeakSolutions
public import HeatKernel.Kernel.CovariantKernelMeasureLimit

/-! # A conservative locally weak kernel for concrete horizontal heat flow

One kernel witness carries the classical and locally weak equations,
conservation, covariance, and initial convergence.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter RothschildStein
open scoped Topology BigOperators
namespace HeatKernel

/-- Almost-everywhere scalar sections of concrete horizontal heat flow determine one conservative covariant smooth evaluation kernel. -/
theorem exists_conservative_localWeak_global_horizontal_kernel_of_ae_sections {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (U : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin (1 + n) → ℝ) → ℝ)
    (hU : ∀ f, LocallyIntegrableOn (U f) {z | 0 < z 0} volume)
    (hslice : ∀ f, ∀ᵐ t ∂volume, 0 < t →
      (fun x => U f ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume]
        globalHorizontalHeatOperator G hq t.toNNReal f) :
    let T := fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal
    ∃ p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => p z.1 z.2.1 z.2.2)
        (Set.Ioi 0 ×ˢ Set.univ) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ t x y, p t x y = p t y x) ∧
      (∀ s t, 0 < s → 0 < t → ∀ x y, ∫ z, p s x z * p t z y = p (s + t) x y) ∧
      (∀ t, 0 < t → ∀ x, MemLp (p t x) 2 volume) ∧
      (∀ t, 0 < t → ∀ x (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
        Integrable (fun y => p t x y * f y) volume) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
        (fun x => ∫ y, p t x y * f y) =ᵐ[volume] T t f) ∧
      (∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun z : ℝ × (Fin n → ℝ) => ∫ y, p z.1 z.2 y * f y) {z | 0 < z.1}) ∧
      (∀ t, 0 < t → ∀ x y, deriv (fun s => p s x y) t =
        sumSquares (G.horizontalFields hq) (fun z => p t x z) y) ∧
      (∀ t, 0 < t → ∀ x y, deriv (fun s => p s x y) t =
        sumSquares (G.horizontalFields hq) (fun z => p t z y) x) ∧
      (∀ I : TopologicalSpace.Opens ℝ, ∀ V : TopologicalSpace.Opens (Fin n → ℝ),
        (∀ t ∈ I, 0 < t) → ∀ x,
        IsLocalWeakSolution G hq hqpos hw hspan
          (fun _ _ i j => if i = j then 1 else 0) I V (fun t y => p t x y)) ∧
      (∀ I : TopologicalSpace.Opens ℝ, ∀ V : TopologicalSpace.Opens (Fin n → ℝ),
        (∀ t ∈ I, 0 < t) → ∀ y,
        IsLocalWeakSolution G hq hqpos hw hspan
          (fun _ _ i j => if i = j then 1 else 0) I V (fun t x => p t x y)) ∧
      (∀ t, 0 < t → ∀ a x y, p t (G.mul a x) (G.mul a y) = p t x y) ∧
      (∀ r t, 0 < r → 0 < t → ∀ x y,
        p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
          (r ^ G.homogeneousDimension)⁻¹ * p t x y) ∧
      (∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
        Tendsto (fun t => eLpNorm (fun x => (∫ y, p t x y * f y) - f x) 2 volume)
          (𝓝[>] 0) (𝓝 0)) ∧
      (∀ φ : (Fin n → ℝ) → ℝ, Continuous φ →
        (∃ C : ℝ, ∀ y, |φ y| ≤ C) → ∀ x,
        Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x))) ∧
      ∃ hnonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y,
      ∃ hint : ∀ t, 0 < t → ∀ x, Integrable (p t x) volume,
      ∃ hmass : ∀ t, 0 < t → ∀ x, (∫ y, p t x y) = 1,
        (∀ x, Tendsto (positiveTimeKernelProbabilityMeasure volume (fun t => p t x)
          (fun t ht => hint t ht x) (fun t ht => hnonneg t ht x)
          (fun t ht => hmass t ht x) x) (𝓝[>] 0)
          (𝓝 ((Measure.dirac x).toProbabilityMeasure))) := by
  let T := fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal
  obtain ⟨u, hu, hrep, hsmooth, _hheat, hkernel, hint, hmass, hdelta, hleft, hscale⟩ :=
    exists_conservative_global_horizontal_kernel_of_ae_sections G hq hw hspan U hU hslice
  rcases hkernel with ⟨hp, hpos, hsym, hcomp, hL2, hintL2, hpoint, hAE, hrow, hcol, hstrongKernel⟩
  let p := evaluationKernel (heatRepresentativeEvaluation T u hu hrep)
  refine ⟨p, hp, hpos, hsym, hcomp, hL2, hintL2, hAE, ?_, hrow, hcol, ?_, ?_, hleft, hscale, hstrongKernel, hdelta, (fun t _ y z => hpos t y z), hint, hmass, ?_⟩
  · intro f
    exact (hsmooth f).congr (fun z hz => hpoint z.1 hz z.2 f)
  · intro I V hI x
    exact isLocalWeakSolution_row_of_joint_smooth_kernel G hq hqpos hw hspan p hp hrow I V hI x
  · intro I V hI y
    exact isLocalWeakSolution_column_of_joint_smooth_kernel G hq hqpos hw hspan p hp hcol I V hI y
  · intro x
    exact tendsto_kernel_probabilityMeasures_of_covariance_and_unit_mass G p hint
      (fun t _ y z => hpos t y z) hmass hleft hscale x

end HeatKernel
