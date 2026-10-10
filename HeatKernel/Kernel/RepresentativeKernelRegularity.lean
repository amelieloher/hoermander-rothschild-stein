-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HeatEvaluations
public import HeatKernel.Kernel.CompactKernelBounds

/-! # Regularity of kernels from continuous representatives

Positive-time scalar continuity gives measurable evaluations after extension by
zero. A countable Hilbert basis then gives joint measurability of the kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)

/-- Each positive-time kernel row is continuous. -/
theorem continuous_heatRepresentativeKernel_row {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    Continuous (fun y => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) := by
  simp_rw [evaluationKernel_eq_evaluation,
    heatRepresentativeEvaluation_apply T u hu hae (half_pos ht)]
  exact hu _ (half_pos ht) _

/-- Scalar evaluations remain continuous on the positive-time domain. -/
theorem continuousOn_heatRepresentativeEvaluation_apply
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1}) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      heatRepresentativeEvaluation T u hu hae p.1 p.2 f) {p | 0 < p.1} := by
  apply (hjoint f).congr
  intro p hp
  exact heatRepresentativeEvaluation_apply T u hu hae hp p.2 f

/-- Extending positive-time evaluations by zero gives measurable scalar functions. -/
theorem measurable_heatRepresentativeEvaluation_apply
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1}) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    Measurable (fun p : ℝ × (Fin n → ℝ) =>
      heatRepresentativeEvaluation T u hu hae p.1 p.2 f) := by
  apply measurable_of_restrict_of_restrict_compl
    (isOpen_lt continuous_const continuous_fst).measurableSet
  · exact (continuousOn_heatRepresentativeEvaluation_apply T u hu hae hjoint f).domRestrict.measurable
  · have heq : ({p : ℝ × (Fin n → ℝ) | 0 < p.1}ᶜ).domRestrict
        (fun p => heatRepresentativeEvaluation T u hu hae p.1 p.2 f) = fun _ => 0 := by
      funext p
      simp only [Set.domRestrict_apply]
      have hp : ¬0 < (p.val).1 := p.property
      simp [heatRepresentativeEvaluation, hp]
    rw [heq]
    exact measurable_const

/-- A countable Hilbert basis makes the representative kernel jointly measurable. -/
theorem measurable_heatRepresentativeKernel_of_basis {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1}) :
    Measurable (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 p.2.1 p.2.2) :=
  measurable_evaluationKernel_of_basis b (heatRepresentativeEvaluation T u hu hae)
    (fun i => measurable_heatRepresentativeEvaluation_apply T u hu hae hjoint (b i))

/-- Jointly continuous representatives give uniform kernel bounds on positive-time compact sets. -/
theorem exists_abs_heatRepresentativeKernel_bound_on_compact
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1})
    {K : Set (ℝ × ((Fin n → ℝ) × (Fin n → ℝ)))} (hK : IsCompact K)
    (hpositive : ∀ p ∈ K, 0 < p.1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K,
      |evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 p.2.1 p.2.2| ≤ C := by
  apply exists_abs_evaluationKernel_bound_on_compact (heatRepresentativeEvaluation T u hu hae) hK
  · intro f
    exact (continuousOn_heatRepresentativeEvaluation_apply T u hu hae hjoint f).comp
      (((continuous_fst.div_const 2).prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun p hp => half_pos (hpositive p hp))
  · intro f
    exact (continuousOn_heatRepresentativeEvaluation_apply T u hu hae hjoint f).comp
      (((continuous_fst.div_const 2).prodMk (continuous_snd.comp continuous_snd)).continuousOn)
      (fun p hp => half_pos (hpositive p hp))

end HeatKernel
