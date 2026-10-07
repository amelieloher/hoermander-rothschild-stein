-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZero
public import RothschildStein.H3.MollifierConvolutionLimit
public import RothschildStein.H1.PrincipalValueDefs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H3

/-- Removing the open unit gauge ball makes every punctured
continuous kernel locally integrable, including type-zero kernels.
BB Proposition 8.49, p. 379; nonsingular part of the PV limit argument. -/
theorem locallyIntegrable_principalValue_far_kernel {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) {K : (Fin N → ℝ) → ℝ}
    (hK : ContinuousOn K ({0}ᶜ : Set (Fin N → ℝ))) :
    LocallyIntegrable ({x | 1 ≤ ν x}.indicator K) volume := by
  rw [locallyIntegrable_iff]
  intro C hC
  have hfar : IsClosed {x | 1 ≤ ν x} := isClosed_le continuous_const ν.gauge.1
  apply (integrableOn_indicator_iff hfar.measurableSet).mpr
  apply ContinuousOn.integrableOn_compact (hC.inter_left hfar)
  apply hK.mono
  intro x hx
  change x ≠ 0
  intro he
  subst x
  have hz := (ν.gauge.2.2.1 0).mpr rfl
  change 1 ≤ ν 0 ∧ 0 ∈ C at hx
  rw [hz] at hx
  norm_num at hx

private theorem principalValueFar_eq_convolution {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (K f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    H1.principalValueFar G ν K f x =
      G2.groupConvolution G f ({w | 1 ≤ ν w}.indicator K) x := by
  rw [G2.groupConvolution_def]
  have he : (fun w => f (G.mul x (G.inv w)) * ({w | 1 ≤ ν w}.indicator K) w) =
      {w | 1 ≤ ν w}.indicator (fun w => K w * f (G.mul x (G.inv w))) := by
    funext w
    by_cases hw : 1 ≤ ν w <;> simp [hw, mul_comm]
  rw [he, integral_indicator (isClosed_le continuous_const ν.gauge.1).measurableSet]
  rfl

/-- The far term of the actual principal-value convolution
converges for actual mollified compact continuous inputs (BB p. 379). -/
theorem tendsto_principalValueFar_groupRegularize {N : ℕ} (G : HomogeneousGroup N)
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    {K f : (Fin N → ℝ) → ℝ} (hK : ContinuousOn K ({0}ᶜ : Set (Fin N → ℝ)))
    (hf : Continuous f) (hc : HasCompactSupport f) (x : Fin N → ℝ) :
    Tendsto (fun ε : ℝ => H1.principalValueFar G ν K (G2.groupRegularize G φ f ε) x)
      (𝓝[>] 0) (𝓝 (H1.principalValueFar G ν K f x)) := by
  simp only [principalValueFar_eq_convolution]
  exact tendsto_groupConvolution_groupRegularize G φ hf hc
    (locallyIntegrable_principalValue_far_kernel G ν hK) x

end RothschildStein.H3
