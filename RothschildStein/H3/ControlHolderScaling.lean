-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderSimilarity
public import RothschildStein.H3.ControlMetric
public import RothschildStein.G2.DilationMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Exact supremum and Hölder seminorm dilation identities for
the control-gauge metric and inverse-image domain (BB p. 339).
The control-norm comparison identifies this metric with the fixed control distance. -/
theorem control_holderNorm_dilate
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {R : ℝ} (hR : 0 < R) (δ : ℝ≥0)
    (A : Set (ControlCarrier N)) (f : ControlCarrier N → ℝ) :
    letI : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    H2.holderSemi δ A f < ⊤ →
      H2.holderSup ((fun x : ControlCarrier N => G.dilate R x) ⁻¹' A)
        (fun x => f (G.dilate R x)) = H2.holderSup A f ∧
      H2.holderSemi δ ((fun x : ControlCarrier N => G.dilate R x) ⁻¹' A)
        (fun x => f (G.dilate R x)) =
        ENNReal.ofReal (R ^ (δ : ℝ)) * H2.holderSemi δ A f := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hf
  have hsur : Function.Surjective (fun x : ControlCarrier N => G.dilate R x) :=
    (G2.dilate_bijective G hR.ne').surjective
  refine ⟨holderSup_surjective_pullback (X := ControlCarrier N) (Y := ControlCarrier N) _ hsur A f, ?_⟩
  apply holderSemi_similarity_pullback (X := ControlCarrier N) (Y := ControlCarrier N) _ hsur hR _ δ A f hf
  intro x y
  exact G2.gaugeDistance_dilate G ν.gauge R hR x y

/-- Left translations preserve the full Hölder norm on the exact
inverse-image domain for every bounded Hölder input (BB p. 339). -/
theorem control_holderNorm_leftTranslation
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (z : Fin N → ℝ) (δ : ℝ≥0)
    (A : Set (ControlCarrier N)) (f : ControlCarrier N → ℝ) :
    letI : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    H2.holderSemi δ A f < ⊤ →
      H2.boundedHolderNorm δ ((fun x : ControlCarrier N => G.mul z x) ⁻¹' A)
        (fun x => f (G.mul z x)) = H2.boundedHolderNorm δ A f := by
  let : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hf
  have hsur : Function.Surjective (fun x : ControlCarrier N => G.mul z x) := by
    intro y
    refine ⟨G.mul (G.inv z) y, ?_⟩
    exact (G.assoc z (G.inv z) y).symm.trans
      ((congrArg (fun a => G.mul a y) (G.inverse_right z)).trans (G.zero_left y))
  have hs := holderSup_surjective_pullback (X := ControlCarrier N) (Y := ControlCarrier N) _ hsur A f
  have hh := holderSemi_similarity_pullback (X := ControlCarrier N) (Y := ControlCarrier N) _ hsur (show (0 : ℝ) < 1 by norm_num)
    (fun x y => by
      change G2.gaugeDistance G ν (G.mul z x) (G.mul z y) =
        1 * G2.gaugeDistance G ν x y
      simpa only [one_mul] using G2.gaugeDistance_leftInvariant G ν x y z) δ A f hf
  have hh' : H2.holderSemi δ ((fun x : ControlCarrier N => G.mul z x) ⁻¹' A)
      (f ∘ (fun x : ControlCarrier N => G.mul z x)) = H2.holderSemi δ A f := by
    simpa only [Real.one_rpow, ENNReal.ofReal_one, one_mul] using hh
  exact congrArg₂ (fun a b : ℝ≥0∞ => a + b) hs hh'

end RothschildStein.H3
