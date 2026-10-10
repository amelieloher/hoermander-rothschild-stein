-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealInvariantSubspace
public import HeatKernel.Semigroup.ScalarMultipliers
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Real subspaces and continuous functional calculus

Real polynomial approximation on the unit interval shows that a self-adjoint complex
operator preserving a closed real subspace also preserves it under real continuous
functional calculus.
-/

@[expose] public section

open Set
open scoped ComplexStarModule

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mapsTo_cfc_of_mapsTo (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (hinv : MapsTo T S S)
    (hspec : spectrum ℝ T ⊆ Icc (0 : ℝ) 1) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) : MapsTo (cfc f T : E →L[ℂ] E) S S := by
  intro x hx
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  let δ := ε / (‖x‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδ
  refine ⟨(Polynomial.aeval T p) x, mapsTo_aeval_of_mapsTo S T hinv p hx, ?_⟩
  have hf' := hf.mono hspec
  have hp' : ContinuousOn p.eval (spectrum ℝ T) := p.continuous.continuousOn
  have hnorm : ‖cfc f T - Polynomial.aeval T p‖ ≤ δ := by
    rw [← cfc_polynomial p T hT, ← cfc_sub f p.eval T hf' hp']
    apply norm_cfc_le hδ.le
    intro r hr
    simpa only [Real.norm_eq_abs, abs_sub_comm] using (hp r (hspec hr)).le
  have hδeq : δ * (‖x‖ + 1) = ε := div_mul_cancel₀ ε (by positivity)
  calc
    dist ((cfc f T) x) ((Polynomial.aeval T p) x) =
        ‖(cfc f T - Polynomial.aeval T p) x‖ := by rw [dist_eq_norm, sub_apply]
    _ ≤ ‖cfc f T - Polynomial.aeval T p‖ * ‖x‖ :=
      (cfc f T - Polynomial.aeval T p).le_opNorm x
    _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ < ε := by nlinarith

end HeatKernel
