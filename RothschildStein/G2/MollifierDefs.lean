-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionDefs
public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.G2
variable {N : ℕ}

/-- The normalized compact smooth bump used in BB Prop 3.48,
p. 121. No symmetry or invariant differential regularity is imposed. -/
structure GroupMollifier (G : HomogeneousGroup N) (ν : HomogeneousNorm G) where
  toFun : (Fin N → ℝ) → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compact : HasCompactSupport toFun
  nonneg : ∀ x, 0 ≤ toFun x
  integral_eq_one : (∫ x, toFun x) = 1
  vanish : ∀ x, 1 ≤ ν x → toFun x = 0

instance GroupMollifier.instCoeFun {G : HomogeneousGroup N} {ν : HomogeneousNorm G} :
    CoeFun (GroupMollifier G ν) (fun _ => (Fin N → ℝ) → ℝ) := ⟨GroupMollifier.toFun⟩

/-- The anisotropically scaled bump ε^{-Q} φ(D_{1/ε}x)
(BB Prop 3.48, p. 121). Its analytic properties require ε > 0. -/
def groupMollifierScale (G : HomogeneousGroup N) (φ : (Fin N → ℝ) → ℝ)
    (ε : ℝ) (x : Fin N → ℝ) : ℝ :=
  (ε ^ G.homogeneousDimension)⁻¹ * φ (G.dilate ε⁻¹ x)

/-- Left regularization by the scaled group bump (BB (3.30), p. 121). -/
def groupRegularize (G : HomogeneousGroup N) (φ f : (Fin N → ℝ) → ℝ)
    (ε : ℝ) : (Fin N → ℝ) → ℝ :=
  groupConvolution G (groupMollifierScale G φ ε) f

end RothschildStein.G2
