-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartImageVolume
public import RothschildStein.G4.WeightedBoxVolume
public import RothschildStein.G4.ActualFrameJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- The actual coordinate Jacobian is the determinant used by
Lebesgue change of variables (BB Theorem 9.12, p. 405). -/
theorem coordinateDerivativeMatrix_det {n : ℕ}
    (T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    Matrix.det (coordinateDerivativeMatrix T) = T.det := by
  have hm : coordinateDerivativeMatrix T = LinearMap.toMatrix' T.toLinearMap := by
    ext i j
    rfl
  rw [hm]
  exact LinearMap.det_toMatrix' T.toLinearMap

/-- An actual injective weighted chart with the source's
factor-four Jacobian bounds has the stated two-sided volume estimate.
The coefficient box and derivative hypotheses use the same radius
(BB Theorem 9.12, p. 405). -/
theorem actual_weighted_chart_volume_bounds {n : ℕ}
    (w : Fin n → ℕ+) {r d : ℝ} (hr : 0 < r)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox w r))
    (hinj : InjOn F (weightedBox w r))
    (hjac : ∀ u ∈ weightedBox w r,
      d / 4 ≤ |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
      |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4 * d) :
    ENNReal.ofReal (d / 4) *
        ENNReal.ofReal (2 ^ n * r ^ (∑ i, (w i : ℕ))) ≤
      volume (F '' weightedBox w r) ∧
    volume (F '' weightedBox w r) ≤ ENNReal.ofReal (4 * d) *
        ENNReal.ofReal (2 ^ n * r ^ (∑ i, (w i : ℕ))) := by
  have hQ := isOpen_weightedBox w r
  have hd : ∀ u ∈ weightedBox w r, HasFDerivAt F (fderiv ℝ F u) u :=
    fun u hu => ((hF.contDiffAt (hQ.mem_nhds hu)).differentiableAt (by simp)).hasFDerivAt
  have hh := chart_image_volume_bounds hQ.measurableSet F (fderiv ℝ F) hd hinj
    (fun u hu => by simpa only [coordinateDerivativeMatrix_det] using (hjac u hu).1)
    (fun u hu => by simpa only [coordinateDerivativeMatrix_det] using (hjac u hu).2)
  simpa only [volume_weightedBox w hr.le] using hh

end RothschildStein.G4
