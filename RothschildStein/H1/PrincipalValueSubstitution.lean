-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueTruncatedIntegrability
public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

private theorem truncation_indicator_comp
    (ν F ψ : (Fin N → ℝ) → ℝ) (ε : ℝ) (x : Fin N → ℝ) :
    ({w | ε < ν w}.indicator (fun w => F w * ψ (G.mul x (G.inv w)))) ∘
      (fun y => G.mul (G.inv y) x) =
    {y | ε < ν (G.mul (G.inv y) x)}.indicator
      (fun y => ψ y * F (G.mul (G.inv y) x)) := by
  funext y
  simp only [Function.comp_apply, Set.indicator_apply, Set.mem_ofPred_eq,
    G2.inv_product, G2.inv_inv, ← G2.mul_assoc, G2.mul_inv, G2.zero_mul]
  split_ifs <;> ring

/-- The actual first BB convolution truncation agrees
with the second formula, including outside absolute integrability. -/
theorem principalValue_firstTruncation_eq
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (ε : ℝ) (x : Fin N → ℝ) :
    (∫ y in {y | ε < ν (G.mul (G.inv y) x)}, ψ y * F (G.mul (G.inv y) x)) =
      principalValueTruncation G ν F ψ ε x := by
  have hp := G2.measurePreserving_invRightAt G x
  have he : MeasurableEmbedding (fun y : Fin N → ℝ => G.mul (G.inv y) x) :=
    hp.measurable.measurableEmbedding
      ((G2.rightTranslation_bijective G x).comp (G2.inv_bijective G)).injective
  have hm : MeasurableSet {w | ε < ν w} := (isOpen_lt continuous_const hν.1).measurableSet
  have hmy : MeasurableSet {y | ε < ν (G.mul (G.inv y) x)} := hm.preimage hp.measurable
  have hi := hp.integral_comp he
    ({w | ε < ν w}.indicator (fun w => F w * ψ (G.mul x (G.inv w))))
  change (∫ y, (({w | ε < ν w}.indicator (fun w => F w * ψ (G.mul x (G.inv w)))) ∘
      (fun y => G.mul (G.inv y) x)) y) = _ at hi
  rw [truncation_indicator_comp G ν F ψ ε x, integral_indicator hmy, integral_indicator hm] at hi
  exact hi

/-- Absolute convergence holds for the fixed first
convolution formula at every positive truncation. -/
theorem integrableOn_principalValue_firstTruncation
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    IntegrableOn (fun y => ψ y * F (G.mul (G.inv y) x))
      {y | ε < ν (G.mul (G.inv y) x)} volume := by
  have hp := G2.measurePreserving_invRightAt G x
  have hm : MeasurableSet {w | ε < ν w} := (isOpen_lt continuous_const hν.1).measurableSet
  have hmy : MeasurableSet {y | ε < ν (G.mul (G.inv y) x)} := hm.preimage hp.measurable
  have hi := (integrableOn_principalValue_truncation G hν hF hc hs hε x).integrable_indicator hm
  have hj := hp.integrable_comp_of_integrable hi
  rw [truncation_indicator_comp G ν F ψ ε x, integrable_indicator_iff hmy] at hj
  exact hj

end RothschildStein.H1
