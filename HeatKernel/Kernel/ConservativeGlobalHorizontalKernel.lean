-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalHorizontalEvaluationKernel
public import HeatKernel.Kernel.SubmarkovIntertwining
public import HeatKernel.Kernel.GlobalHorizontalHeatCovariance
public import HeatKernel.Kernel.GlobalHorizontalHeatRepresentatives
public import HeatKernel.Kernel.GlobalHorizontalHeatOrder

/-! # Conservation and covariance of the concrete evaluation kernel

The concrete sub-Markov semigroup and horizontal form covariance give unit mass,
translation invariance, parabolic scaling, and the bounded continuous initial limit.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter RothschildStein
open scoped Topology BigOperators
namespace HeatKernel

/-- Almost-everywhere scalar sections of concrete horizontal heat flow determine one conservative covariant smooth evaluation kernel. -/
theorem exists_conservative_global_horizontal_kernel_of_ae_sections {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (U : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin (1 + n) → ℝ) → ℝ)
    (hU : ∀ f, LocallyIntegrableOn (U f) {z | 0 < z 0} volume)
    (hslice : ∀ f, ∀ᵐ t ∂volume, 0 < t →
      (fun x => U f ((timeSpaceCoordinates n).symm (t, x))) =ᵐ[volume]
        globalHorizontalHeatOperator G hq t.toNNReal f) :
    let T := fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal
    ∃ u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ,
    ∃ hu : ∀ t, 0 < t → ∀ f, Continuous (u t f),
    ∃ hrep : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f,
      (∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × (Fin n → ℝ) => u z.1 f z.2) {z | 0 < z.1}) ∧
      (∀ t, 0 < t → ∀ f x,
        deriv (fun s => u s f x) t = sumSquares (G.horizontalFields hq) (u t f) x) ∧
      let p := evaluationKernel (heatRepresentativeEvaluation T u hu hrep)
      (ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => p z.1 z.2.1 z.2.2)
        (Set.Ioi 0 ×ˢ Set.univ) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ t x y, p t x y = p t y x) ∧
      (∀ s t, 0 < s → 0 < t → ∀ x y, ∫ z, p s x z * p t z y = p (s + t) x y) ∧
      (∀ t, 0 < t → ∀ x, MemLp (fun y => p t x y) 2 volume) ∧
      (∀ t, 0 < t → ∀ x (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
        Integrable (fun y => p t x y * f y) volume) ∧
      (∀ t, 0 < t → ∀ x (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))),
        ∫ y, p t x y * f y = u t f x) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
        (fun x => ∫ y, p t x y * f y) =ᵐ[volume] T t f) ∧
      (∀ t, 0 < t → ∀ x y, deriv (fun s => p s x y) t =
        sumSquares (G.horizontalFields hq) (fun z => p t x z) y) ∧
      (∀ t, 0 < t → ∀ x y, deriv (fun s => p s x y) t =
        sumSquares (G.horizontalFields hq) (fun z => p t z y) x) ∧
      (∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
        Tendsto (fun t => eLpNorm (fun x => (∫ y, p t x y * f y) - f x) 2 volume)
          (𝓝[>] 0) (𝓝 0))) ∧
      (∀ t, 0 < t → ∀ x, Integrable (p t x) volume) ∧
      (∀ t, 0 < t → ∀ x, ∫ y, p t x y = 1) ∧
      (∀ φ : (Fin n → ℝ) → ℝ, Continuous φ →
        (∃ C : ℝ, ∀ y, |φ y| ≤ C) → ∀ x,
        Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ t, 0 < t → ∀ a x y, p t (G.mul a x) (G.mul a y) = p t x y) ∧
      (∀ r t, 0 < r → 0 < t → ∀ x y,
        p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
          (r ^ G.homogeneousDimension)⁻¹ * p t x y) := by
  let T := fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal
  have hself (s : ℝ) (_hs : 0 ≤ s) : IsSelfAdjoint (T s) :=
    globalHorizontalHeatOperator_isSelfAdjoint G hq s.toNNReal
  have hsemigroup (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : T (s + t) = (T s).comp (T t) := by
    change globalHorizontalHeatOperator G hq (s + t).toNNReal = _
    rw [Real.toNNReal_add hs ht, globalHorizontalHeatOperator_add]
  have hpositive (t : ℝ) (_ht : 0 < t) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
      (hf : ∀ᵐ x ∂volume, 0 ≤ f x) : ∀ᵐ x ∂volume, 0 ≤ T t f x :=
    globalHorizontalHeatOperator_nonneg G hq t.toNNReal f hf
  have hstrong (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
      Tendsto (fun t => T t f) (𝓝[>] 0) (𝓝 f) := tendsto_globalHorizontalHeatOperator_zero G hq f
  have hmarkov (t : ℝ) (_ht : 0 < t) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
      (hf : ∀ᵐ x ∂volume, 0 ≤ f x ∧ f x ≤ 1) : ∀ᵐ x ∂volume, 0 ≤ T t f x ∧ T t f x ≤ 1 :=
    globalHorizontalHeatOperator_submarkov G hq t.toNNReal f hf
  have hcomm (s : ℝ) (_hs : 0 < s) (a : Fin n → ℝ)
      (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
      T s (leftTranslationL2 G a f) = leftTranslationL2 G a (T s f) :=
    globalHorizontalHeatOperator_leftTranslation_realTime G hq a s f
  have hdilate (r : ℝ) (hr : 0 < r) (s : ℝ) (_hs : 0 < s)
      (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
      T s (dilationL2Equiv G hr f) = dilationL2Equiv G hr (T (r ^ 2 * s) f) :=
    globalHorizontalHeatOperator_dilation_realTime G hq hw hr s f
  obtain ⟨u, hu, hrep, hsmooth, hheat, hkernel⟩ :=
    exists_global_horizontal_evaluation_kernel_of_ae_sections G hq hspan U hU hslice
  refine ⟨u, hu, hrep, hsmooth, hheat, hkernel, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact (integrable_heatRepresentativeKernel_row_of_submarkov T u hu hrep hself hsemigroup
      hmarkov ht (heatRepresentativeKernel_nonneg T u hu hrep hpositive t) x).1
  · intro t ht x
    exact integral_heatRepresentativeKernel_eq_one_of_submarkov_intertwining G T u hu hrep
      hself hsemigroup (fun f => (hsmooth f).continuousOn) hpositive hmarkov hcomm hdilate hstrong ht x
  · intro φ hφ hbounded x
    exact tendsto_heatRepresentativeKernel_integral_of_submarkov_intertwining G T u hu hrep
      hself hsemigroup (fun f => (hsmooth f).continuousOn) hpositive hmarkov hcomm hdilate hstrong
      hφ hbounded x
  · intro t ht a x y
    exact heatRepresentativeKernel_left_invariant G T u hu hrep hcomm ht a x y
  · intro r t hr ht x y
    exact heatRepresentativeKernel_parabolic_scaling G T u hu hrep hr ht (hdilate r hr) x y

end HeatKernel
