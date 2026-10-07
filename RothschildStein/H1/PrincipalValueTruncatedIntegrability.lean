-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ConvolutionParameterSupport
public import RothschildStein.H1.PuncturedProductIntegrability
public import RothschildStein.H1.PrincipalValueDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Every positive-radius truncation is absolutely
integrable, since the translated test is compactly supported
and the integration region stays away from zero (BB p. 277). -/
theorem integrableOn_principalValue_truncation
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    IntegrableOn (fun w => F w * ψ (G.mul x (G.inv w))) {w | ε < ν w} volume := by
  have hD : Continuous (fun w => ψ (G.mul x (G.inv w))) :=
    hc.comp ((G2.continuous_mul G).comp (continuous_const.prodMk (G2.continuous_inv G)))
  have hν0 : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have hi := integrableOn_punctured_mul_compact hF hD
    (hasCompactSupport_leftInv_translate G hs x) (isClosed_le continuous_const hν.1)
    (show (0 : Fin N → ℝ) ∉ {w | ε ≤ ν w} by simpa only [mem_ofPred_eq, hν0] using not_le.mpr hε)
  exact hi.mono_set (fun _ hw => hw.le)

/-- The far term is absolutely integrable at every base point. -/
theorem integrableOn_principalValue_far
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    IntegrableOn (fun w => F w * ψ (G.mul x (G.inv w))) {w | 1 ≤ ν w} volume := by
  have hD : Continuous (fun w => ψ (G.mul x (G.inv w))) :=
    hc.comp ((G2.continuous_mul G).comp (continuous_const.prodMk (G2.continuous_inv G)))
  have hν0 : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  exact integrableOn_punctured_mul_compact hF hD
    (hasCompactSupport_leftInv_translate G hs x) (isClosed_le continuous_const hν.1)
    (by simp only [mem_ofPred_eq, hν0]; norm_num)

end RothschildStein.H1
