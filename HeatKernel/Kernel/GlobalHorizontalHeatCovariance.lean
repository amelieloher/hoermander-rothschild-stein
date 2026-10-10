-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HorizontalHeatRealization
public import HeatKernel.Kernel.NativeComplexSpatialPullbacks
public import HeatKernel.Kernel.RealHorizontalHeatCovariance

/-! # Covariance of concrete full-volume horizontal heat flow

The native complex realization transfers the horizontal resolvent covariance
to the concrete full-volume heat family, including at zero time.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Concrete full-volume horizontal heat flow commutes with left translation. -/
theorem globalHorizontalHeatOperator_leftTranslation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (a : Fin n → ℝ)
    (t : ℝ≥0) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalHorizontalHeatOperator G hq t (leftTranslationL2 G a f) =
      leftTranslationL2 G a (globalHorizontalHeatOperator G hq t f) := by
  have h := transportedRealHeatOperator_horizontal_leftTranslation G hq a
    (realL2Subspace (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))))
    (isClosed_realL2Subspace _)
    (complexL2Extension _ (horizontalFormResolvent ⊤ (G.horizontalFields hq)))
    (horizontalFormResolvent_complex_isSelfAdjoint ⊤ (G.horizontalFields hq))
    (mapsTo_complexL2Extension_realL2Subspace _ _)
    (spectrum_horizontalFormResolvent_complex_subset ⊤ (G.horizontalFields hq))
    (globalSpatialRealSubspaceEquiv n)
    exists_nativeComplexSpatial_real_imaginary_decomposition
    (globalSpatialRealSubspaceEquiv_resolvent G hq)
    (nativeComplexLeftTranslationL2 G a) (nativeComplexLeftTranslationL2_real_embedding G a) t f
  simpa only [← globalHorizontalHeatOperator_eq_transport] using h

/-- Concrete full-volume horizontal heat flow rescales time under normalized dilation. -/
theorem globalHorizontalHeatOperator_dilation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (t : ℝ≥0) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalHorizontalHeatOperator G hq t (dilationL2Equiv G hr f) =
      dilationL2Equiv G hr
        (globalHorizontalHeatOperator G hq (NNReal.mk (r ^ 2) (sq_nonneg r) * t) f) := by
  have h := transportedRealHeatOperator_horizontal_dilation G hq hw hr
    (realL2Subspace (volume.restrict ((⊤ : Opens (Fin n → ℝ)) : Set (Fin n → ℝ))))
    (isClosed_realL2Subspace _)
    (complexL2Extension _ (horizontalFormResolvent ⊤ (G.horizontalFields hq)))
    (horizontalFormResolvent_complex_isSelfAdjoint ⊤ (G.horizontalFields hq))
    (mapsTo_complexL2Extension_realL2Subspace _ _)
    (spectrum_horizontalFormResolvent_complex_subset ⊤ (G.horizontalFields hq))
    (globalSpatialRealSubspaceEquiv n)
    exists_nativeComplexSpatial_real_imaginary_decomposition
    (globalSpatialRealSubspaceEquiv_resolvent G hq)
    (nativeComplexDilationL2 G hr) (nativeComplexDilationL2_real_embedding G hr) t f
  simpa only [← globalHorizontalHeatOperator_eq_transport] using h

/-- Real-time horizontal heat flow commutes with left translation. -/
theorem globalHorizontalHeatOperator_leftTranslation_realTime {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (a : Fin n → ℝ)
    (t : ℝ) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalHorizontalHeatOperator G hq t.toNNReal (leftTranslationL2 G a f) =
      leftTranslationL2 G a (globalHorizontalHeatOperator G hq t.toNNReal f) :=
  globalHorizontalHeatOperator_leftTranslation G hq a t.toNNReal f

/-- Real-time horizontal heat flow has the literal squared-dilation time covariance. -/
theorem globalHorizontalHeatOperator_dilation_realTime {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r)
    (t : ℝ) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalHorizontalHeatOperator G hq t.toNNReal (dilationL2Equiv G hr f) =
      dilationL2Equiv G hr (globalHorizontalHeatOperator G hq (r ^ 2 * t).toNNReal f) := by
  have htime : NNReal.mk (r ^ 2) (sq_nonneg r) * t.toNNReal = (r ^ 2 * t).toNNReal := by
    rw [Real.toNNReal_mul (sq_nonneg r)]
    congr 1
    apply NNReal.eq
    exact (Real.coe_toNNReal (r ^ 2) (sq_nonneg r)).symm
  simpa only [htime] using globalHorizontalHeatOperator_dilation G hq hw hr t.toNNReal f

end HeatKernel
