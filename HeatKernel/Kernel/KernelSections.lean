-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.RepresentativeKernelRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Spacetime sections of representative kernels

A positive time split expresses a kernel section as a semigroup representative
of a fixed Riesz vector. Smoothness of representatives then gives smoothness of
each fixed-endpoint spacetime section.
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

include hself hsemigroup

/-- Splitting time identifies the kernel with a representative of a fixed Riesz vector. -/
theorem heatRepresentativeKernel_add_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : Fin n → ℝ) :
    evaluationKernel (heatRepresentativeEvaluation T u hu hae) (s + t) x y =
      u t (evaluationVector (heatRepresentativeEvaluation T u hu hae s) x) y := by
  rw [← inner_evaluationVector_eq_kernel_of_semigroup
    (heatRepresentativeEvaluation T u hu hae) T hself
    (fun s t hs ht x f => heatRepresentativeEvaluation_add T u hu hae hsemigroup hs ht x f)
    hsemigroup hs ht x y, real_inner_comm, inner_evaluationVector,
    heatRepresentativeEvaluation_apply T u hu hae ht]

/-- A fixed time split gives a smooth section after that split time. -/
theorem contDiffOn_heatRepresentativeKernel_after
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 x p.2) {p | s < p.1} := by
  have hshift : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => (p.1 - s, p.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have h := (hsmooth (evaluationVector (heatRepresentativeEvaluation T u hu hae s) x)).comp
    hshift.contDiffOn (fun p hp => sub_pos.mpr hp)
  apply h.congr
  intro p hp
  have heq := heatRepresentativeKernel_add_eq T u hu hae hself hsemigroup hs
    (sub_pos.mpr hp) x p.2
  change evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 x p.2 =
    u (p.1 - s) (evaluationVector (heatRepresentativeEvaluation T u hu hae s) x) p.2
  have htime : s + (p.1 - s) = p.1 := by ring
  rwa [htime] at heq

/-- Each fixed-endpoint spacetime section is smooth for all positive times. -/
theorem contDiffOn_heatRepresentativeKernel_section
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    (x : Fin n → ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 x p.2) {p | 0 < p.1} := by
  apply (isOpen_lt continuous_const continuous_fst).contDiffOn_iff.mpr
  intro p hp
  have hs : 0 < p.1 / 2 := half_pos hp
  have hp' : p.1 / 2 < p.1 := half_lt_self hp
  exact (contDiffOn_heatRepresentativeKernel_after T u hu hae hself hsemigroup hsmooth hs x).contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hp')

/-- Symmetry gives smoothness of the section with the other spatial endpoint fixed. -/
theorem contDiffOn_heatRepresentativeKernel_other_section
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    (y : Fin n → ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 p.2 y) {p | 0 < p.1} := by
  simp_rw [evaluationKernel_symm (heatRepresentativeEvaluation T u hu hae) _ _ y]
  exact contDiffOn_heatRepresentativeKernel_section T u hu hae hself hsemigroup hsmooth y

end HeatKernel
