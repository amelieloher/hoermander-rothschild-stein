-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelSections
public import RothschildStein.Definitions.sumSquares
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Pointwise heat equations for representative kernels

A fixed positive time split expresses each kernel section as a time translate
of a semigroup representative. Its classical heat equation transfers through
that identity, and symmetry gives the equation in the other spatial variable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

open RothschildStein

variable {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hheat : ∀ t, 0 < t → ∀ f y,
      deriv (fun s => u s f y) t = sumSquares X (u t f) y)

include hself hsemigroup hheat

/-- The heat equation for semigroup representatives transfers to each kernel row. -/
theorem deriv_heatRepresentativeKernel_eq_sumSquares_row {t : ℝ} (ht : 0 < t)
    (x y : Fin n → ℝ) :
    deriv (fun s => evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x y) t =
      sumSquares X (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x z) y := by
  let f := evaluationVector (heatRepresentativeEvaluation T u hu hae (t / 2)) x
  have heq (s : ℝ) (hs : t / 2 < s) (z : Fin n → ℝ) :
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x z = u (s - t / 2) f z := by
    have h := heatRepresentativeKernel_add_eq T u hu hae hself hsemigroup (half_pos ht)
      (sub_pos.mpr hs) x z
    have htime : t / 2 + (s - t / 2) = s := by ring
    rwa [htime] at h
  have hhalf : t / 2 < t := by linarith
  have hgerm : (fun s => evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x y)
      =ᶠ[𝓝 t] (fun s => u (s - t / 2) f y) :=
    (eventually_gt_nhds hhalf).mono fun s hs => heq s hs y
  rw [hgerm.deriv_eq, deriv_comp_sub_const (fun s => u s f y),
    hheat _ (sub_pos.mpr hhalf)]
  exact congrArg (fun v => sumSquares X v y) (funext fun z => (heq t hhalf z).symm)

/-- Symmetry gives the classical heat equation in the first spatial variable. -/
theorem deriv_heatRepresentativeKernel_eq_sumSquares_column {t : ℝ} (ht : 0 < t)
    (x y : Fin n → ℝ) :
    deriv (fun s => evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x y) t =
      sumSquares X (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t z y) x := by
  have htime : (fun s => evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x y) =
      (fun s => evaluationKernel (heatRepresentativeEvaluation T u hu hae) s y x) :=
    funext fun s => evaluationKernel_symm _ s x y
  have hspace : (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t y z) =
      (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t z y) :=
    funext fun z => evaluationKernel_symm _ t y z
  rw [htime, ← hspace]
  exact deriv_heatRepresentativeKernel_eq_sumSquares_row X T u hu hae hself hsemigroup hheat ht y x

end HeatKernel
