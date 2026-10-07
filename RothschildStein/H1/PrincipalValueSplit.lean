-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OpenShellBoundary
public import RothschildStein.H1.PrincipalValueNearIntegrability
public import RothschildStein.H1.PrincipalValueTruncatedIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Shell cancellation gives the exact subtracted
near-shell plus far-term formula for every positive truncation below
one (BB Proposition 6.29, p. 277). -/
theorem principalValueTruncation_eq_subtractedShell_add_far
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (x : Fin N → ℝ) :
    principalValueTruncation G ν F ψ ε x =
      (∫ w in {w | ε < ν w ∧ ν w < 1}, F w * (ψ (G.mul x (G.inv w)) - ψ x)) +
        principalValueFar G ν F ψ x := by
  let A := {w | ε < ν w ∧ ν w < 1}
  let B := {w | 1 ≤ ν w}
  have hiA : IntegrableOn (fun w => F w * ψ (G.mul x (G.inv w))) A volume :=
    (integrableOn_principalValue_truncation G hν hF hc.continuous hs hε x).mono_set (fun _ hw => hw.1)
  have hiB : IntegrableOn (fun w => F w * ψ (G.mul x (G.inv w))) B volume :=
    integrableOn_principalValue_far G hν hF hc.continuous hs x
  have hiSub : IntegrableOn (fun w => F w * (ψ (G.mul x (G.inv w)) - ψ x)) A volume :=
    (integrableOn_principalValue_near G hν hF hhom hc hs x).mono_set (fun _ hw => hw.2.le)
  have hiF : IntegrableOn F A volume :=
    (integrableOn_gaugeShell hν hF hε).mono_set (fun _ hw => ⟨hw.1.le, hw.2.le⟩)
  have hShell : (∫ w in A, F w * ψ (G.mul x (G.inv w))) =
      ∫ w in A, F w * (ψ (G.mul x (G.inv w)) - ψ x) := by
    have he : (fun w => F w * ψ (G.mul x (G.inv w))) =
        fun w => F w * (ψ (G.mul x (G.inv w)) - ψ x) + ψ x * F w := by funext w; ring
    have hz : (∫ w in A, F w) = 0 := by
      change (∫ w in {w | ε < ν w ∧ ν w < 1}, F w) = 0
      rw [integral_openGaugeShell_eq_closed G hν hε (by norm_num)]
      exact hcancel ε 1 hε hε1
    rw [he, integral_add hiSub (hiF.const_mul (ψ x)), integral_const_mul, hz, mul_zero, add_zero]
  have hSet : {w | ε < ν w} = A ∪ B := by
    ext w
    change (ε < ν w) ↔ ((ε < ν w ∧ ν w < 1) ∨ 1 ≤ ν w)
    constructor
    · intro hw
      rcases lt_or_ge (ν w) 1 with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr h
    · intro hw
      exact hw.elim And.left (fun h => hε1.trans_le h)
  have hDis : Disjoint A B := Set.disjoint_left.mpr fun _ hwA hwB => (not_lt_of_ge hwB) hwA.2
  unfold principalValueTruncation principalValueFar
  rw [hSet, setIntegral_union hDis (isClosed_le continuous_const hν.1).measurableSet hiA hiB, hShell]

end RothschildStein.H1
