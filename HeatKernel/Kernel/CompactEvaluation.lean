-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.LocalRestriction
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Bounded evaluation of continuous L² representatives on Euclidean space

The induced measure on a set contained in the closure of its interior has full support.
Closed balls therefore supply compact comparison spaces for bounding point evaluation.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Full support passes to measurable subsets contained in the closure of their interior. -/
theorem isOpenPosMeasure_comap_subtype_of_subset_closure_interior {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] (K : Set X) (hK : MeasurableSet K)
    (hregular : K ⊆ closure (interior K)) : (μ.comap (Subtype.val : K → X)).IsOpenPosMeasure := by
  constructor
  intro U hU hnonempty
  rw [(MeasurableEmbedding.subtype_coe hK).comap_apply]
  rcases isOpen_induced_iff.mp hU with ⟨V, hV, rfl⟩
  obtain ⟨x, hx⟩ := hnonempty
  have hnon : (V ∩ interior K).Nonempty :=
    mem_closure_iff.mp (hregular x.property) V hV hx
  have hsubset : V ∩ interior K ⊆ Subtype.val '' (Subtype.val ⁻¹' V : Set K) := by
    intro y hy
    exact ⟨⟨y, interior_subset hy.2⟩, hy.1, rfl⟩
  exact ne_of_gt ((hV.inter isOpen_interior).measure_pos μ hnon |>.trans_le (measure_mono hsubset))

/-- A compact set containing a dense interior gives local uniform representative bounds. -/
theorem exists_bound_continuous_representatives_on_regular_compact {X H : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (K : Set X) (hK : MeasurableSet K) (hcompact : IsCompact K)
    (hregular : K ⊆ closure (interior K))
    (B : H →L[ℝ] Lp ℝ 2 μ) (u : H → X → ℝ)
    (hu : ∀ f, ContinuousOn (u f) K) (hae : ∀ f, B f =ᵐ[μ] u f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f x, x ∈ K → ‖u f x‖ ≤ C * ‖f‖ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let : IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : K → X)) :=
    IsFiniteMeasureOnCompacts.comap' μ continuous_subtype_val (MeasurableEmbedding.subtype_coe hK)
  let := isOpenPosMeasure_comap_subtype_of_subset_closure_interior μ K hK hregular
  exact exists_bound_continuous_representatives_on_compact μ K hK B u hu hae

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Closed balls give uniform bounds for continuous representatives of a bounded Euclidean L² map. -/
theorem exists_bound_continuous_representatives_on_closedBall {n : ℕ}
    (B : H →L[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : H → (Fin n → ℝ) → ℝ) (a : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hu : ∀ f, ContinuousOn (u f) (Metric.closedBall a r))
    (hae : ∀ f, B f =ᵐ[volume] u f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f x, x ∈ Metric.closedBall a r → ‖u f x‖ ≤ C * ‖f‖ := by
  apply exists_bound_continuous_representatives_on_regular_compact volume
    (Metric.closedBall a r) measurableSet_closedBall (isCompact_closedBall a r) ?_ B u hu hae
  rw [interior_closedBall a hr.ne', closure_ball a hr.ne']

/-- Point evaluation of continuous representatives of a bounded Euclidean L² map. -/
def euclideanL2RepresentativeEvaluation {n : ℕ}
    (B : H →L[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : H → (Fin n → ℝ) → ℝ) (hu : ∀ f, Continuous (u f))
    (hae : ∀ f, B f =ᵐ[volume] u f) (x : Fin n → ℝ) : H →L[ℝ] ℝ := by
  let L := continuousRepresentativeLinearMap volume B.toLinearMap u hu hae
  let l : H →ₗ[ℝ] ℝ :=
    { toFun := fun f => L f x
      map_add' := fun f g => by simp
      map_smul' := fun a f => by simp }
  have hbound := exists_bound_continuous_representatives_on_closedBall B u x
    (by norm_num : (0 : ℝ) < 1) (fun f => (hu f).continuousOn) hae
  exact l.mkContinuous hbound.choose (fun f => hbound.choose_spec.2 f x (by simp))

@[simp] theorem euclideanL2RepresentativeEvaluation_apply {n : ℕ}
    (B : H →L[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : H → (Fin n → ℝ) → ℝ) (hu : ∀ f, Continuous (u f))
    (hae : ∀ f, B f =ᵐ[volume] u f) (x : Fin n → ℝ) (f : H) :
    euclideanL2RepresentativeEvaluation B u hu hae x f = u f x := rfl

end HeatKernel
