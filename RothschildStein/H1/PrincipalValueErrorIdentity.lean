-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The truncation error is exactly the omitted
subtracted integral over the small gauge ball. -/
theorem principalValueTruncation_sub_eq_neg_smallIntegral
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (x : Fin N → ℝ) :
    principalValueTruncation G ν F ψ ε x - principalValueConvolution G ν F ψ x =
      -(∫ w in {w | ν w ≤ ε}, F w * (ψ (G.mul x (G.inv w)) - ψ x)) := by
  let f := fun w => F w * (ψ (G.mul x (G.inv w)) - ψ x)
  let A := {w | ν w ≤ ε}
  let B := {w | ε < ν w ∧ ν w < 1}
  have hi := integrableOn_principalValue_near G hν hF hhom hc hs x
  have hiA : IntegrableOn f A volume := hi.mono_set fun _ hw => hw.trans hε1.le
  have hiB : IntegrableOn f B volume := hi.mono_set fun _ hw => hw.2.le
  have hset : {w | ν w < 1} = A ∪ B := by
    ext w
    change ν w < 1 ↔ ν w ≤ ε ∨ (ε < ν w ∧ ν w < 1)
    constructor
    · intro hw
      rcases le_or_gt (ν w) ε with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hw⟩
    · intro hw
      exact hw.elim (fun h => h.trans_lt hε1) And.right
  have hd : Disjoint A B := Set.disjoint_left.mpr fun _ ha hb => (not_lt_of_ge ha) hb.1
  have hn : principalValueNear G ν F ψ x = (∫ w in A, f w) + ∫ w in B, f w := by
    unfold principalValueNear
    rw [hset, setIntegral_union hd
      ((isOpen_lt continuous_const hν.1).inter (isOpen_lt hν.1 continuous_const)).measurableSet hiA hiB]
  rw [principalValueTruncation_eq_subtractedShell_add_far G hν hF hhom hcancel hc hs hε hε1]
  unfold principalValueConvolution
  rw [hn]
  change (∫ w in B, f w) + principalValueFar G ν F ψ x -
    ((∫ w in A, f w) + (∫ w in B, f w) + principalValueFar G ν F ψ x) = -(∫ w in A, f w)
  ring

end RothschildStein.H1
