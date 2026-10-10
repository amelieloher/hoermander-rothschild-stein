-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TransportedHeatCovariance
public import HeatKernel.Kernel.ComplexHorizontalHeatCovariance

/-! # Covariance of the transported real horizontal heat family

Compatible complex horizontal resolvents and group actions give real
translation commutation and parabolic dilation of the heat operators.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein
open scoped NNReal

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Compatible complex horizontal translations give translation covariance of the real heat family. -/
theorem transportedRealHeatOperator_horizontal_leftTranslation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ)
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) (hinv : Set.MapsTo Q S S)
    (hσ : spectrum ℝ Q ⊆ Set.Icc (0 : ℝ) 1)
    (e : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) ≃ₗᵢ[ℝ] S)
    (hspan : ∀ z : E, ∃ a b, z = (e a : E) + Complex.I • (e b : E))
    (hres : ∀ f, (e (globalHorizontalFormResolvent G hq f) : E) = Q (e f))
    (W : E ≃ₗᵢ[ℂ] E) (hW : ∀ f, W (e f : E) = (e (leftTranslationL2 G y f) : E))
    (t : ℝ≥0) (f : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) :
    transportedRealHeatOperator S hS Q hQ hinv hσ e t (leftTranslationL2 G y f) =
      leftTranslationL2 G y (transportedRealHeatOperator S hS Q hQ hinv hσ e t f) := by
  have hcov (v : E) : heatOperator Q t (W v) = W (heatOperator Q (1 * t) v) := by
    simpa only [one_mul] using
      (heatOperator_horizontal_leftTranslation_of_complex_extension G hq y
        (S.subtypeL.comp e.toContinuousLinearEquiv.toContinuousLinearMap) hspan Q hQ hσ
        (fun v => (hres v).symm) W hW t v)
  simpa only [one_mul] using
    (transportedRealHeatOperator_unitary_of_ambient_covariance S hS Q hQ hinv hσ e
      (leftTranslationL2 G y) W hW 1 t hcov f)

/-- Compatible complex horizontal dilations give parabolic covariance of the real heat family. -/
theorem transportedRealHeatOperator_horizontal_dilation {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) (hinv : Set.MapsTo Q S S)
    (hσ : spectrum ℝ Q ⊆ Set.Icc (0 : ℝ) 1)
    (e : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) ≃ₗᵢ[ℝ] S)
    (hspan : ∀ z : E, ∃ a b, z = (e a : E) + Complex.I • (e b : E))
    (hres : ∀ f, (e (globalHorizontalFormResolvent G hq f) : E) = Q (e f))
    (W : E ≃ₗᵢ[ℂ] E) (hW : ∀ f, W (e f : E) = (e (dilationL2Equiv G hr f) : E))
    (t : ℝ≥0) (f : Lp ℝ 2 (volume : Measure (Fin N → ℝ))) :
    transportedRealHeatOperator S hS Q hQ hinv hσ e t (dilationL2Equiv G hr f) =
      dilationL2Equiv G hr
        (transportedRealHeatOperator S hS Q hQ hinv hσ e (NNReal.mk (r ^ 2) (sq_nonneg r) * t) f) := by
  apply transportedRealHeatOperator_unitary_of_ambient_covariance S hS Q hQ hinv hσ e
    (dilationL2Equiv G hr) W hW (NNReal.mk (r ^ 2) (sq_nonneg r)) t ?_ f
  intro v
  exact heatOperator_horizontal_dilation_of_complex_extension G hq hw hr
    (S.subtypeL.comp e.toContinuousLinearEquiv.toContinuousLinearMap) hspan Q hQ hσ
    (fun v => (hres v).symm) W hW t v

end HeatKernel
