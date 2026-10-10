-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.L2KernelRepresentation
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Tensor-tested initial conditions for representative kernels

The all-point L² representation identifies iterated kernel pairings with Hilbert
pairings. Strong continuity therefore gives the tensor-tested initial condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

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

/-- The positive-time kernel represents the prescribed continuous semigroup version everywhere. -/
theorem integral_heatRepresentativeKernel_mul_L2 {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    ∫ y, evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y * f y = u t f x := by
  rw [integral_evaluationKernel_mul_L2_of_ae_eq _ x
    (ae_heatRepresentativeKernel_eq_evaluationVector T u hu hae hself hsemigroup ht x),
    heatRepresentativeEvaluation_apply T u hu hae ht]

end HeatKernel
