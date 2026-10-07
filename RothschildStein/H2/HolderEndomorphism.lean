-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderModule
public import RothschildStein.H2.PrincipalValueLinear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A pointwise linear operator preserving the Hölder class induces
an endomorphism of the normalized concrete module. -/
def holderEndomorphism {δ : ℝ≥0} {U : Set X} (F : (X → ℝ) → X → ℝ)
    (hmap : ∀ f, BoundedHolder δ U f → BoundedHolder δ U (F f))
    (hadd : ∀ f g, BoundedHolder δ U f → BoundedHolder δ U g →
      ∀ x ∈ U, F (f + g) x = F f x + F g x)
    (hsmul : ∀ c f, ∀ x ∈ U, F (c • f) x = c * F f x) :
    holderFunctions δ U →ₗ[ℝ] holderFunctions δ U where
  toFun f := holderNormalize (hmap f f.property.1)
  map_add' f g := by
    apply Subtype.ext
    funext x
    change U.indicator (F ((f + g : holderFunctions δ U) : X → ℝ)) x =
      U.indicator (F f) x + U.indicator (F g) x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
      have he : ((f + g : holderFunctions δ U) : X → ℝ) = (f : X → ℝ) + (g : X → ℝ) := rfl
      rw [he, hadd f g f.property.1 g.property.1 x hx]
    · simp only [indicator_of_notMem hx, zero_add]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change U.indicator (F ((c • f : holderFunctions δ U) : X → ℝ)) x =
      c * U.indicator (F f) x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
      have he : ((c • f : holderFunctions δ U) : X → ℝ) = c • (f : X → ℝ) := rfl
      rw [he, hsmul c f x hx]
    · simp only [indicator_of_notMem hx, mul_zero]

omit [MeasurableSpace X] [BorelSpace X] in
/-- An extended Hölder norm bound becomes a bound for the finite seminorm. -/
theorem holderEndomorphism_seminorm_le {δ : ℝ≥0} {U : Set X}
    (T : holderFunctions δ U →ₗ[ℝ] holderFunctions δ U) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f, boundedHolderNorm δ U (T f) ≤ ENNReal.ofReal C * boundedHolderNorm δ U f)
    (f : holderFunctions δ U) :
    holderFunctionSeminorm δ U (T f) ≤ C * holderFunctionSeminorm δ U f := by
  have he := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top f.property.1).ne (hbound f)
  change (boundedHolderNorm δ U (T f)).toReal ≤ C * (boundedHolderNorm δ U f).toReal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using he

end RothschildStein.H2
