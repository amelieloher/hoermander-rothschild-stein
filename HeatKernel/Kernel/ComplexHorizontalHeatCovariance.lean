-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ComplexifiedGraphCovariance
public import HeatKernel.Kernel.GlobalHorizontalCovariance
public import HeatKernel.Kernel.GraphHeatOperatorCovariance

/-! # Horizontal heat covariance through compatible complex extensions

The concrete real horizontal form graph supplies heat covariance once
its resolvent and group actions have compatible complex extensions.
The real-imaginary decomposition and compatibility identities are explicit.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein
open scoped NNReal

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A compatible complex extension of left translation commutes with the horizontal heat operators. -/
theorem heatOperator_horizontal_leftTranslation_of_complex_extension {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ)
    (j : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ] E)
    (hspan : ∀ z : E, ∃ a b, z = j a + Complex.I • j b)
    (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) (hσ : spectrum ℝ Q ⊆ Set.Icc (0 : ℝ) 1)
    (hres : ∀ f, Q (j f) = j (globalHorizontalFormResolvent G hq f))
    (e : E ≃ₗᵢ[ℂ] E) (he : ∀ f, e (j f) = j (leftTranslationL2 G y f))
    (t : ℝ≥0) (v : E) : heatOperator Q t (e v) = e (heatOperator Q t v) := by
  have hg : ∀ u g, Q (u + g) = u → Q (e u + (1 : ℝ) • e g) = e u :=
    complexified_resolvent_scaled_graph_map j hspan (globalHorizontalFormResolvent G hq)
      (leftTranslationL2 G y).toContinuousLinearEquiv.toContinuousLinearMap Q
      e.toContinuousLinearEquiv.toContinuousLinearMap hres he 1
      (fun u g hu => by
        change InverseResolventGraph (globalHorizontalFormResolvent G hq)
          (leftTranslationL2 G y u) ((1 : ℝ) • leftTranslationL2 G y g)
        simpa only [one_smul] using
          inverseResolventGraph_globalHorizontalForm_leftTranslation G hq y hu)
  simpa only [one_mul] using
    heatOperator_apply_unitary_of_scaled_graph_map e Q hQ hσ (c := 1) (by norm_num) hg t v

/-- A compatible complex extension of normalized dilation rescales horizontal heat time by its squared factor. -/
theorem heatOperator_horizontal_dilation_of_complex_extension {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (j : Lp ℝ 2 (volume : Measure (Fin N → ℝ)) →L[ℝ] E)
    (hspan : ∀ z : E, ∃ a b, z = j a + Complex.I • j b)
    (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) (hσ : spectrum ℝ Q ⊆ Set.Icc (0 : ℝ) 1)
    (hres : ∀ f, Q (j f) = j (globalHorizontalFormResolvent G hq f))
    (e : E ≃ₗᵢ[ℂ] E) (he : ∀ f, e (j f) = j (dilationL2Equiv G hr f))
    (t : ℝ≥0) (v : E) :
    heatOperator Q t (e v) = e (heatOperator Q (NNReal.mk (r ^ 2) (sq_nonneg r) * t) v) := by
  have hg : ∀ u g, Q (u + g) = u → Q (e u + r ^ 2 • e g) = e u :=
    complexified_resolvent_scaled_graph_map j hspan (globalHorizontalFormResolvent G hq)
      (dilationL2Equiv G hr).toContinuousLinearEquiv.toContinuousLinearMap Q
      e.toContinuousLinearEquiv.toContinuousLinearMap hres he (r ^ 2)
      (fun _ _ => inverseResolventGraph_globalHorizontalForm_dilation G hq hw hr)
  exact heatOperator_apply_unitary_of_scaled_graph_map e Q hQ hσ
    (c := NNReal.mk (r ^ 2) (sq_nonneg r)) (show (0 : ℝ) < r ^ 2 from pow_pos hr _) hg t v

end HeatKernel
