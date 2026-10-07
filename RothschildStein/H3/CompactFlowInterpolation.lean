-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FlowStepInterpolation
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- Smooth compactly supported inputs satisfy the positive-step estimate
 under the global group-flow hypothesis. Smoothness and compact support
 supply the required Lp integrability. -/
theorem field_step_interpolation_compact_of_group_integralCurve {n : ℕ}
    (G : HomogeneousGroup n) (E : ℝ → (Fin n → ℝ))
    (hE : Continuous E) (hE0 : E 0 = 0)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hflow : ∀ x, IsIntegralCurve (fun t => G.mul x (E t)) (fun _ => V))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) {ε : ℝ} (hε : 0 < ε) :
    MemLp (fieldDerivative V u) p volume ∧
      eLpNorm (fieldDerivative V u) p volume ≤
        ENNReal.ofReal (2/ε) * eLpNorm u p volume +
        ENNReal.ofReal (ε/2) *
          eLpNorm (fieldDerivative V (fieldDerivative V u)) p volume := by
  have hdu : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative V u) :=
    contDiffOn_univ.mp (RothschildStein.S.contDiffOn_fieldDerivative ⊤ V u
      hV.contDiffOn hu.contDiffOn)
  have hddu : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative V (fieldDerivative V u)) :=
    contDiffOn_univ.mp (RothschildStein.S.contDiffOn_fieldDerivative ⊤ V _
      hV.contDiffOn hdu.contDiffOn)
  have hs := (RothschildStein.S.tsupport_fieldDerivative_subset V (fieldDerivative V u)).trans
    (RothschildStein.S.tsupport_fieldDerivative_subset V u)
  have hc : HasCompactSupport (fieldDerivative V (fieldDerivative V u)) :=
    huc.of_isClosed_subset (isClosed_tsupport _) hs
  exact field_step_interpolation_of_group_integralCurve G E hE hE0 V hV hflow hp hpt hu
    (hu.continuous.memLp_of_hasCompactSupport huc)
    (hddu.continuous.memLp_of_hasCompactSupport hc) hε

end RothschildStein.H3
