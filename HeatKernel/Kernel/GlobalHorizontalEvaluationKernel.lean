-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelProductSmoothness
public import HeatKernel.Kernel.KernelHeatEquation
public import HeatKernel.Kernel.KernelStrongContinuity
public import HeatKernel.Kernel.L2Positivity
public import HeatKernel.Kernel.L2KernelComposition
public import HeatKernel.Kernel.GlobalHorizontalHeatRepresentatives
public import HeatKernel.Kernel.GlobalHorizontalHeatOrder

/-! # A concrete evaluation kernel from almost-everywhere orbit sections

The actual horizontal semigroup supplies symmetry, composition, positivity,
and strong continuity. Locally integrable scalar orbit sections determine
smooth representatives and their common evaluation kernel.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter RothschildStein
open scoped Topology BigOperators
namespace HeatKernel

/-- Almost-everywhere scalar sections of concrete horizontal heat flow determine one smooth evaluation kernel. -/
theorem exists_global_horizontal_evaluation_kernel_of_ae_sections {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
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
      ContDiffOn ℝ (⊤ : ℕ∞)
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
          (𝓝[>] 0) (𝓝 0)) := by
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
  have hex (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :=
    exists_smooth_global_horizontal_heat_representative_of_ae_sections G hq hspan f
      (U f) (hU f) (hslice f)
  choose v hv huv hsections hcoordinateHeat hunique using hex
  let u := fun t f x => v f ((timeSpaceCoordinates n).symm (t, x))
  have hmem (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
      0 < (timeSpaceCoordinates n).symm (t, x) 0 := by
    simpa only [timeSpaceCoordinates_symm_time] using ht
  have hsmooth (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) => u z.1 f z.2) {z | 0 < z.1} :=
    (hv f).comp (timeSpaceCoordinates n).symm.contDiff.contDiffOn (fun p hp => hmem p.1 hp p.2)
  have hu (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
      Continuous (u t f) := by
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (u t f) Set.univ :=
      (hv f).comp ((timeSpaceCoordinates n).symm.contDiff.comp
        (contDiff_const.prodMk contDiff_id)).contDiffOn (fun x _ => hmem t ht x)
    exact (contDiffOn_univ.mp hs).continuous
  have hrep (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
      T t f =ᵐ[volume] u t f := by
    obtain ⟨h, heq⟩ := hsections f t ht
    have hc := h.coeFn_toLp
    rw [heq] at hc
    exact hc
  have hheat (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
      (x : Fin n → ℝ) : deriv (fun s => u s f x) t =
        sumSquares (G.horizontalFields hq) (u t f) x :=
    deriv_eq_sumSquares_of_coordinate_heat_equation (G.horizontalFields hq)
      (G.horizontalFields_contDiff hq) (v f) (hv f) (hcoordinateHeat f) ht x
  refine ⟨u, hu, hrep, hsmooth, hheat, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_heatRepresentativeKernel_positive G hq hspan T u hu hrep
      hself hsemigroup hsmooth hheat
  · exact heatRepresentativeKernel_nonneg T u hu hrep hpositive
  · exact evaluationKernel_symm _
  · intro s t hs ht x y
    exact integral_heatRepresentativeKernel_mul T u hu hrep hself hsemigroup hs ht x y
  · intro t ht x
    exact memLp_evaluationKernel_of_ae_eq _ x
      (ae_heatRepresentativeKernel_eq_evaluationVector T u hu hrep hself hsemigroup ht x)
  · intro t ht x f
    exact integrable_evaluationKernel_mul_L2_of_ae_eq _ x
      (ae_heatRepresentativeKernel_eq_evaluationVector T u hu hrep hself hsemigroup ht x) f
  · intro t ht x f
    exact integral_heatRepresentativeKernel_mul_L2 T u hu hrep hself hsemigroup ht x f
  · intro t ht f
    exact ae_integral_heatRepresentativeKernel_mul_L2 T u hu hrep hself hsemigroup ht f
  · intro t ht x y
    exact deriv_heatRepresentativeKernel_eq_sumSquares_row
      (G.horizontalFields hq) T u hu hrep hself hsemigroup hheat ht x y
  · intro t ht x y
    exact deriv_heatRepresentativeKernel_eq_sumSquares_column
      (G.horizontalFields hq) T u hu hrep hself hsemigroup hheat ht x y
  · exact tendsto_eLpNorm_integral_heatRepresentativeKernel_sub_L2
      T u hu hrep hself hsemigroup hstrong

end HeatKernel
