-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.L2KernelRepresentation

/-! # Integrable composition of L² evaluation kernels

Lebesgue L² pairings supply both integrability and the all-point semigroup
composition identity for kernels constructed from continuous representatives.
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

/-- Continuous representative kernels satisfy the semigroup composition identity everywhere. -/
theorem integral_heatRepresentativeKernel_mul {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : Fin n → ℝ) :
    ∫ z, evaluationKernel (heatRepresentativeEvaluation T u hu hae) s x z *
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t z y =
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) (s + t) x y := by
  apply integral_evaluationKernel_mul_of_pairing volume
    (heatRepresentativeEvaluation T u hu hae) T (fun f => (f : (Fin n → ℝ) → ℝ)) hself
    (fun s t hs ht x f => heatRepresentativeEvaluation_add T u hu hae hsemigroup hs ht x f)
    hsemigroup ?_ ?_ hs ht x y
  · intro t ht f
    simpa only [heatRepresentativeEvaluation_apply T u hu hae ht] using (hae t ht f).symm
  · intro f g
    simp [L2.inner_def, mul_comm]

end HeatKernel
