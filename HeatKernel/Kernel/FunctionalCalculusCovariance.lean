-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # Unitary covariance of continuous functional calculus

Conjugation by an isometric linear equivalence commutes with continuous functional calculus.
A scalar composition identity then transports a conjugation identity for a resolvent to one
for a continuous function of the resolvent.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real continuous functional calculus commutes with unitary conjugation. -/
theorem conjStarAlgEquiv_cfc (e : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ A)) :
    e.conjStarAlgEquiv (cfc f A) = cfc f (e.conjStarAlgEquiv A) := by
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) e.conjStarAlgEquiv f A hf
    e.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous hA
    (IsSelfAdjoint.map e.conjStarAlgEquiv hA)

/-- A continuous scalar composition identity transports unitary covariance. -/
theorem conjStarAlgEquiv_cfc_eq_of_comp (e : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (f g h : ℝ → ℝ) (hf : Continuous f)
    (hg : ContinuousOn g (spectrum ℝ A))
    (he : e.conjStarAlgEquiv A = cfc g A)
    (hcomp : Set.EqOn (f ∘ g) h (spectrum ℝ A)) :
    e.conjStarAlgEquiv (cfc f A) = cfc h A := by
  rw [conjStarAlgEquiv_cfc e A hA f hf.continuousOn, he,
    ← cfc_comp f g A hA hf.continuousOn hg]
  exact cfc_congr hcomp

end HeatKernel
