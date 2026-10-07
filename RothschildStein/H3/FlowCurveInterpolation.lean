-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FlowTaylorLp
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- The field-action unit-step interpolation estimate under the global
group-flow hypotheses, using Taylor's identity and the two chain rules. -/
theorem field_unit_interpolation_of_group_integralCurve {n : ℕ}
    (G : HomogeneousGroup n) (E : ℝ → (Fin n → ℝ))
    (hE : Continuous E) (hE0 : E 0 = 0)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hflow : ∀ x, IsIntegralCurve (fun t => G.mul x (E t)) (fun _ => V))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hup : MemLp u p volume)
    (hddp : MemLp (fieldDerivative V (fieldDerivative V u)) p volume) :
    MemLp (fieldDerivative V u) p volume ∧
      eLpNorm (fieldDerivative V u) p volume ≤ 2 * eLpNorm u p volume +
        ENNReal.ofReal (1/2 : ℝ) *
          eLpNorm (fieldDerivative V (fieldDerivative V u)) p volume := by
  have hdu : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative V u) :=
    contDiffOn_univ.mp (RothschildStein.S.contDiffOn_fieldDerivative ⊤ V u
      hV.contDiffOn hu.contDiffOn)
  have hddu : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative V (fieldDerivative V u)) :=
    contDiffOn_univ.mp (RothschildStein.S.contDiffOn_fieldDerivative ⊤ V _
      hV.contDiffOn hdu.contDiffOn)
  apply group_flow_unit_interpolation_of_taylor G E hE.measurable hp hpt
    hu.continuous.stronglyMeasurable hup hddu.continuous.stronglyMeasurable hddp
  intro x
  apply field_flow_taylor_of_derivative_data V u (fun t => G.mul x (E t)) x
  · rw [hE0,RothschildStein.G2.mul_zero]
  · intro t
    simpa only [Function.comp_def,fieldDerivative] using
      (hu.differentiable (by simp) (G.mul x (E t))).hasFDerivAt.comp_hasDerivAt t (hflow x t)
  · intro t
    simpa only [Function.comp_def,fieldDerivative] using
      (hdu.differentiable (by simp) (G.mul x (E t))).hasFDerivAt.comp_hasDerivAt t (hflow x t)
  · exact hddu.continuous.comp
      ((RothschildStein.G2.continuous_mul G).comp (continuous_const.prodMk hE))

end RothschildStein.H3
