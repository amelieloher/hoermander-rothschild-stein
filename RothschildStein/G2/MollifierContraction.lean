-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierIntegrability
public import RothschildStein.G2.YoungLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- The scaled bump has L1 norm one (BB Prop 3.48, p. 121). -/
theorem eLpNorm_groupMollifierScale_one (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) : eLpNorm (groupMollifierScale G φ ε) 1 volume = 1 := by
  have hi := integrable_groupMollifierScale G φ hε
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  have hn : (fun x => ‖groupMollifierScale G φ ε x‖) = groupMollifierScale G φ ε := by
    funext x
    exact Real.norm_of_nonneg (groupMollifierScale_nonneg G φ hε x)
  rw [hn, integral_groupMollifierScale G φ hε, ENNReal.ofReal_one]

/-- Group regularization does not increase any finite Lp norm
(BB Prop 3.48, p. 121, via Young (1,p,p)). -/
theorem eLpNorm_groupRegularize_le_finite (φ : GroupMollifier G ν) {ε : ℝ}
    (hε : 0 < ε) {p : ℝ} (hp : 1 ≤ p) {f : (Fin N → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (groupRegularize G φ f ε) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume := by
  have H := eLpNorm_groupConvolution_le_finite_ae G
    (integrable_groupMollifierScale G φ hε).aestronglyMeasurable hf
    (p := 1) (q := p) (r := p) le_rfl hp hp (by simp)
  simpa only [ENNReal.ofReal_one, eLpNorm_groupMollifierScale_one G φ hε,
    one_mul, groupRegularize] using H

end RothschildStein.G2
