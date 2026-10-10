-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelSections
public import HeatKernel.Kernel.OpenSectionEquality

/-! # Identifying joint kernel representatives pointwise

Smooth fixed-endpoint sections identify any continuous joint representative of
the kernel at every positive time and every spatial pair.
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
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})

include hself hsemigroup hsmooth

/-- A continuous joint representative agrees with the kernel at all positive times and endpoints. -/
theorem heatRepresentativeKernel_eq_joint_representative
    (v : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ)
    (hv : ContinuousOn v ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ))
    (hrep : (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2) =ᵐ[
        (volume.restrict {p : ℝ × (Fin n → ℝ) | 0 < p.1}).prod volume] v) :
    Set.EqOn (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2) v
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) := by
  apply eqOn_continuous_of_ae_eq_of_continuous_sections_on_open volume volume
    (isOpen_lt continuous_const continuous_fst) hrep
  · intro y
    exact (contDiffOn_heatRepresentativeKernel_other_section T u hu hae hself hsemigroup hsmooth y).continuousOn
  · intro p hp
    exact continuous_heatRepresentativeKernel_row T u hu hae hp p.2
  · exact hv

/-- A smooth joint representative transfers smoothness to the original kernel witness. -/
theorem contDiffOn_heatRepresentativeKernel_of_joint_representative
    (v : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ))
    (hrep : (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2) =ᵐ[
        (volume.restrict {p : ℝ × (Fin n → ℝ) | 0 < p.1}).prod volume] v) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2)
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) :=
  hv.congr (heatRepresentativeKernel_eq_joint_representative T u hu hae hself hsemigroup
    hsmooth v hv.continuousOn hrep)

end HeatKernel
