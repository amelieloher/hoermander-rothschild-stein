-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.RegularizedPotentialSplit
public import RothschildStein.H1.CriticalCutoffMoment
public import RothschildStein.H1.PrincipalValueErrorIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The regularized critical potential equals
PV plus the cutoff moment times the test, minus an explicitly
subtracted small-ball error. -/
theorem criticalRegularizedPotential_eq_PV_moment_sub_error
    {ν F η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hη : Continuous η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hRε : R * ε < 1)
    (hηout : ∀ w, R ≤ ν w → η w = 0)
    (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) (x : Fin N → ℝ) :
    G2.groupConvolution G ψ (fun w => F w * (1 - η (G.dilate ε⁻¹ w))) x =
      principalValueConvolution G ν F ψ x + ψ x * (∫ v in {v | ν v ≤ R}, F v * (1 - η v)) -
        ∫ w in {w | ν w ≤ R * ε}, η (G.dilate ε⁻¹ w) * (F w * (ψ (G.mul x (G.inv w)) - ψ x)) := by
  let S := {w | ν w ≤ R * ε}
  let D := fun w => F w * (ψ (G.mul x (G.inv w)) - ψ x)
  let ηs := fun w => η (G.dilate ε⁻¹ w)
  let θs := fun w => 1 - ηs w
  have hηs : Continuous ηs := hη.comp (G2.continuous_dilate G ε⁻¹)
  have hθs : Continuous θs := continuous_const.sub hηs
  have heθ : θs =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
    filter_upwards [cutoff_comp_dilate_eventually_one G heη ε⁻¹] with w hw
    change 1 - η (G.dilate ε⁻¹ w) = 0
    change η (G.dilate ε⁻¹ w) = 1 at hw
    rw [hw, sub_self]
  have hreg : Continuous (fun w => F w * θs w) := continuous_puncturedKernel_mul_cutoff hF hθs heθ
  have hK : IsCompact S := G2.isCompact_gauge_le hν (R * ε)
  have hiM : IntegrableOn (fun w => F w * θs w) S volume := hreg.continuousOn.integrableOn_compact hK
  have hiD : IntegrableOn D S volume :=
    (integrableOn_principalValue_near G hν hF hhom hcψ hsψ x).mono_set (fun _ hw => hw.trans hRε.le)
  have hiE : IntegrableOn (fun w => ηs w * D w) S volume :=
    hiD.continuousOn_mul hηs.continuousOn hK
  have hefun : (fun w => (F w * θs w) * ψ (G.mul x (G.inv w))) =
      fun w => (D w + ψ x * (F w * θs w)) - ηs w * D w := by
    funext w
    dsimp [D, θs]
    ring
  have hsmall : (∫ w in S, (F w * θs w) * ψ (G.mul x (G.inv w))) =
      (∫ w in S, D w) + ψ x * (∫ w in S, F w * θs w) - ∫ w in S, ηs w * D w := by
    rw [hefun]
    have hsub := integral_sub (hiD.add (hiM.const_mul (ψ x))) hiE
    have hadd := integral_add hiD (hiM.const_mul (ψ x))
    change (∫ w in S, D w + ψ x * (F w * θs w)) =
      (∫ w in S, D w) + ∫ w in S, ψ x * (F w * θs w) at hadd
    change (∫ w in S, (D w + ψ x * (F w * θs w)) - ηs w * D w) =
      (∫ w in S, D w + ψ x * (F w * θs w)) - ∫ w in S, ηs w * D w at hsub
    rw [hadd, integral_const_mul] at hsub
    exact hsub
  have hm : (∫ w in S, F w * θs w) = ∫ v in {v | ν v ≤ R}, F v * (1 - η v) :=
    integral_criticalCutoffMoment_scale G hν hhom hε
  have hsplit := regularizedPotential_eq_truncation_add_smallBall G hν hF hη heη hε hηout hcψ.continuous hsψ x
  change G2.groupConvolution G ψ (fun w => F w * θs w) x =
    principalValueTruncation G ν F ψ (R * ε) x + ∫ w in S, (F w * θs w) * ψ (G.mul x (G.inv w)) at hsplit
  rw [hsmall, hm] at hsplit
  have ht := principalValueTruncation_sub_eq_neg_smallIntegral G hν hF hhom hcancel hcψ hsψ (mul_pos hR hε) hRε x
  change principalValueTruncation G ν F ψ (R * ε) x - principalValueConvolution G ν F ψ x = -(∫ w in S, D w) at ht
  change G2.groupConvolution G ψ (fun w => F w * θs w) x =
    principalValueConvolution G ν F ψ x + ψ x * (∫ v in {v | ν v ≤ R}, F v * (1 - η v)) -
      ∫ w in S, ηs w * D w
  linarith

end RothschildStein.H1
