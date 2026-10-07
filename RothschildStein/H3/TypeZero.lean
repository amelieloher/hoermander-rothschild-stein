-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.GaugeConsequences
public import RothschildStein.G2.Measure
public import RothschildStein.G2.AnalyticStructure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The fixed-gauge mean is taken over the closed unit-to-e shell
(BB Prop 6.26, p. 274). -/
def kernelMean (ν f : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ x in {x | 1 ≤ ν x ∧ ν x ≤ Real.exp 1}, f x

/-- The function version of the type-zero class in Chapter 8:
smoothness off the origin, degree minus Q, and zero fixed-gauge mean
(BB Def. 8.21 and Remark 8.23, p. 354). -/
structure TypeZero (ν f : (Fin N → ℝ) → ℝ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ
  homogeneous : ∀ (t : ℝ), 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
    f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x
  mean_zero : kernelMean ν f = 0

/-- Inversion preserves the mean for a symmetric gauge by invariance of
Haar measure under inversion (BB Prop. 6.26, p. 274). -/
theorem kernelMean_reflection (ν : HomogeneousNorm G) (hν : ν.Symmetric)
    (f : (Fin N → ℝ) → ℝ) :
    kernelMean ν (fun x => f (G.inv x)) = kernelMean ν f := by
  have hm := measurePreserving_inv G
  have he := (continuous_inv G).measurable.measurableEmbedding (inv_bijective G).injective
  have hi := (hm.restrict_preimage_emb he
    {x | 1 ≤ ν x ∧ ν x ≤ Real.exp 1}).integral_comp he f
  have hs (x : Fin N → ℝ) : ν.toFun (G.inv x) = ν.toFun x := hν x
  simpa only [kernelMean, Set.preimage_ofPred_eq, hs] using hi

/-- Reflection preserves the three defining properties of the type-zero
class; the derivative-size bound is a separate hypothesis. -/
theorem TypeZero.reflection {ν : HomogeneousNorm G} (hν : ν.Symmetric)
    {f : (Fin N → ℝ) → ℝ} (hf : TypeZero G ν f) :
    TypeZero G ν (fun x => f (G.inv x)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply hf.smooth.comp (contDiff_inv G).contDiffOn
    intro x hx
    change G.inv x ≠ 0
    change x ≠ 0 at hx
    intro hi
    apply hx
    have h := congrArg G.inv hi
    simpa only [inv_inv, inv_zero] using h
  · intro t ht x hx
    rw [inv_dilate G ht]
    apply hf.homogeneous t ht
    intro hi
    apply hx
    have h := congrArg G.inv hi
    simpa only [inv_inv, inv_zero] using h
  · rw [kernelMean_reflection G ν hν]
    exact hf.mean_zero

end RothschildStein.H3
