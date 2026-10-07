-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.HomogeneousGroup.HasPrincipalValue
public import RothschildStein.Definitions.HomogeneousGroup.inv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ}

/-- The principal-value truncation in the second BB
convolution formula, with the exact argument x∘w⁻¹ (BB p. 277). -/
def principalValueTruncation (G : HomogeneousGroup N)
    (ν F ψ : (Fin N → ℝ) → ℝ) (ε : ℝ) (x : Fin N → ℝ) : ℝ :=
  ∫ w in {w | ε < ν w}, F w * ψ (G.mul x (G.inv w))

/-- The absolutely integrable subtracted near term. -/
def principalValueNear (G : HomogeneousGroup N)
    (ν F ψ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∫ w in {w | ν w < 1}, F w * (ψ (G.mul x (G.inv w)) - ψ x)

/-- The nonsingular far term. -/
def principalValueFar (G : HomogeneousGroup N)
    (ν F ψ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∫ w in {w | 1 ≤ ν w}, F w * ψ (G.mul x (G.inv w))

/-- The continuous principal-value convolution assembled
from the near and far terms (BB Prop 6.29, pp. 276–278). -/
def principalValueConvolution (G : HomogeneousGroup N)
    (ν F ψ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  principalValueNear G ν F ψ x + principalValueFar G ν F ψ x

end RothschildStein.H1
