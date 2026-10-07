-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Foundation
public import Mathlib.Analysis.LConvolution
public import Mathlib.Analysis.Convolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ}

/-- A dedicated subtraction carrier for the group convolution.
Only subtraction and measurable structure are supplied; no commutative group
law is asserted (BB Convention 3.43, Def 3.44, pp. 118–119). -/
def ConvolutionCarrier (_G : HomogeneousGroup N) := Fin N → ℝ

instance convolutionCarrierSub (G : HomogeneousGroup N) : Sub (ConvolutionCarrier G) :=
  ⟨fun x y => G.mul x (G.inv y)⟩
instance convolutionCarrierMeasurableSpace (G : HomogeneousGroup N) :
    MeasurableSpace (ConvolutionCarrier G) := inferInstanceAs (MeasurableSpace (Fin N → ℝ))
instance convolutionCarrierMeasureSpace (G : HomogeneousGroup N) :
    MeasureSpace (ConvolutionCarrier G) := inferInstanceAs (MeasureSpace (Fin N → ℝ))

/-- Nonnegative group convolution, using Mathlib's multiplicative
Lebesgue convolution on the proved group carrier (BB Def 3.44, p. 118). -/
def lgroupConvolution (G : HomogeneousGroup N) (f g : (Fin N → ℝ) → ℝ≥0∞) :
    (Fin N → ℝ) → ℝ≥0∞ :=
  MeasureTheory.mlconvolution (G := Carrier G) f g volume

/-- Real or complex group convolution, defined through Mathlib's
Bochner convolution on the dedicated subtraction carrier. Absolute convergence
is a separate predicate; the default Bochner value carries no convergence claim
(BB Def 3.44 and (3.27), pp. 118–119). -/
def groupConvolution {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)
    (f g : (Fin N → ℝ) → 𝕜) : (Fin N → ℝ) → 𝕜 :=
  MeasureTheory.convolution (G := ConvolutionCarrier G) g f (ContinuousLinearMap.mul ℝ 𝕜) volume

/-- Absolute convergence at a point in BB's original ordering
(BB Def 3.44, pp. 118–119). -/
def GroupConvolutionExistsAt {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)
    (f g : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ) : Prop :=
  Integrable (fun y => f y * g (G.mul (G.inv y) x))

/-- The nonnegative convolution is exactly the BB defining integral
(BB Def 3.44, p. 118). -/
theorem lgroupConvolution_def (G : HomogeneousGroup N) (f g : (Fin N → ℝ) → ℝ≥0∞)
    (x : Fin N → ℝ) :
    lgroupConvolution G f g x = ∫⁻ y, f y * g (G.mul (G.inv y) x) := rfl

/-- The Bochner definition has the second formula of (3.27),
with the first slot differentiated by right-invariant fields (BB p. 119). -/
theorem groupConvolution_def {𝕜 : Type*} [RCLike 𝕜] (G : HomogeneousGroup N)
    (f g : (Fin N → ℝ) → 𝕜) (x : Fin N → ℝ) :
    groupConvolution G f g x = ∫ w, f (G.mul x (G.inv w)) * g w := by
  change (∫ w, g w * f (G.mul x (G.inv w))) = _
  simp only [mul_comm]

end RothschildStein.G2
