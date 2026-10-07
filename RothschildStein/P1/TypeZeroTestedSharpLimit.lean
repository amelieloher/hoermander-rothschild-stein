-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ActualUniformSharpRows
public import RothschildStein.P1.UniformSharpTestedLimit
public import RothschildStein.P1.SharpTestedRowRepresentative
public import RothschildStein.P1.GainWord
public import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Actual tested sharp integrals converge to the
operator action minus its multiplier. Both measurability and the outer
integrable majorant are proved for every interior pair of tests. -/
theorem tendsto_typeZero_tested_sharpIntegral (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F 0) (f g : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ ξ, g ξ * (∫ η in {η | ε < F.rho ξ η}, T.kernel ξ η * f η))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ξ, g ξ * (T.apply f ξ - T.mult ξ * f ξ))) := by
  let D := C.typeZeroInput_uniformSharpRows hF T.isType f g.hasCompactSupport g.tsupport_subset
  have hval (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ tsupport g) :
      D.value ξ = T.apply f ξ - T.mult ξ * f ξ := by
    rw [← (D.limit ξ hξ).limUnder_eq]
    simp only [TypeOperator.apply, TypeOperator.truncated, ite_true, add_sub_cancel_right]
  have hvLocal : LocallyIntegrableOn
      (fun ξ => T.apply f ξ - T.mult ξ * f ξ) (F.V : Set (Fin (n + m) → ℝ)) volume :=
    (T.locallyIntegrableOn_apply_test hF f).sub
      ((T.mult.contDiff.continuous.mul f.contDiff.continuous).continuousOn.locallyIntegrableOn
        F.V.isOpen.measurableSet)
  have hv : Integrable (fun ξ => g ξ * D.value ξ) := by
    apply (S.integrable_mul_test F.V hvLocal g).congr
    apply Eventually.of_forall
    intro ξ
    by_cases hz : g ξ = 0
    · simp only [hz, mul_zero, zero_mul]
    · change (T.apply f ξ - T.mult ξ * f ξ) * g ξ = g ξ * D.value ξ
      rw [hval ξ (subset_tsupport g hz), mul_comm]
  have hm (ε : ℝ) (hε : 0 < ε) : AEStronglyMeasurable
      (fun ξ => g ξ * (∫ η in {η | ε < F.rho ξ η}, T.kernel ξ η * f η)) volume := by
    let d : TypeDecomposition F 0 1 T.kernel := Classical.choice (T.isType 1)
    have hi := C.integrable_sharpTruncated_tested_representative hF.lifted T.isType d H.norm.gauge f g hε
    apply hi.aestronglyMeasurable.integral_prod_right'.congr
    apply Eventually.of_forall
    intro ξ
    have he := C.sharp_tested_row_eq_representative hF.lifted d H.norm.gauge.1 f g ε ξ
    simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using he.symm
  have ht := D.tendsto_tested_integral g (subset_tsupport g)
    (g.contDiff.continuous.integrable_of_hasCompactSupport g.hasCompactSupport) hv hm
  have he : (∫ ξ, g ξ * D.value ξ) = ∫ ξ, g ξ * (T.apply f ξ - T.mult ξ * f ξ) := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro ξ
    by_cases hz : g ξ = 0
    · simp only [hz, zero_mul]
    · change g ξ * D.value ξ = g ξ * (T.apply f ξ - T.mult ξ * f ξ)
      rw [hval ξ (subset_tsupport g hz)]
  rw [he] at ht
  exact ht

end RothschildStein.P1.LiftedChart
