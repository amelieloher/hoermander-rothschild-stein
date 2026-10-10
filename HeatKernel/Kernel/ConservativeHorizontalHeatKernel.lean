-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.LocalWeakGlobalHorizontalKernel
public import HeatKernel.Kernel.HorizontalHeatSpacetimeRepresentative
public import HeatKernel.Kernel.L2ScalarPairings

/-! # The conservative kernel of the horizontal heat semigroup

Joint scalar representatives of the concrete semigroup determine one smooth,
symmetric, conservative kernel with the classical and local weak heat equations.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter RothschildStein
open scoped Topology BigOperators
namespace HeatKernel

/-- Symmetry and square-integrable rows make every positive-time convolution
product integrable at every pair of endpoints. -/
theorem integrable_kernel_convolution_of_symmetric_L2_rows {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (p : ℝ → X → X → ℝ)
    (hsym : ∀ t x y, p t x y = p t y x)
    (hL2 : ∀ t, 0 < t → ∀ x, MemLp (p t x) 2 μ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : X) :
    Integrable (fun z => p s x z * p t z y) μ := by
  have hint := integrable_mul_scalar_L2 ((hL2 s hs x).toLp (p s x)) (hL2 t ht y)
  apply hint.congr
  filter_upwards [(hL2 s hs x).coeFn_toLp] with z hz
  rw [hz, hsym t y z]

/-- The horizontal heat semigroup has a smooth conservative kernel with both local
weak equations, covariance, and strong and pointwise initial convergence. -/
theorem exists_conservative_horizontal_heat_kernel {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq)) :
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
  obtain ⟨U, _hUmeasurable, hU, hslice⟩ :=
    exists_globalHorizontalHeat_spacetime_representative G hq
  exact exists_conservative_localWeak_global_horizontal_kernel_of_ae_sections
    G hq hqpos hw hspan U hU
    (fun f => Filter.Eventually.of_forall (fun t _ht => hslice f t))

end HeatKernel
