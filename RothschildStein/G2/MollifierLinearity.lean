-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Regularization respects differences of Lp inputs pointwise
(BB p. 122; approximation argument). -/
theorem groupRegularize_sub (φ : GroupMollifier G ν) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : (Fin N → ℝ) → ℝ}
    (hf : MemLp f p volume) (hg : MemLp g p volume) :
    groupRegularize G φ (f - g) ε = groupRegularize G φ f ε - groupRegularize G φ g ε := by
  funext x
  have h₁ := groupRegularize_existsAt G φ hε hp hf x
  have h₂ := groupRegularize_existsAt G φ hε hp hg x
  simp only [groupRegularize, groupConvolution_eq_integral, Pi.sub_apply, mul_sub]
  exact integral_sub h₁ h₂

end RothschildStein.G2
