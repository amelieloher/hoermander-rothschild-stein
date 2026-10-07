-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakDerivative
public import RothschildStein.S.IntrinsicUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3
variable {N q : ℕ}

/-- Continuous intrinsic suffix jets suffice for the weak word identity,
using the single-field reverse bridge at each step (BB Prop. 2.22,
pp. 87–90). -/
theorem hasWeakWordDeriv_of_intrinsic_suffix_jets
    (Ω : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (I : List (Fin q)) (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ J, J.IsSuffix I → hasIntrinsicWordDeriv X Ω J f (jet J))
    (hc : ∀ J, J.IsSuffix I → ContinuousOn (jet J) (Ω : Set (Fin N → ℝ))) :
    hasWeakWordDeriv X Ω I f (jet I) := by
  induction I with
  | nil =>
    rw [hzero]
    exact S.hasWeakWordDeriv_nil X Ω
      (by simpa only [hzero] using
        (hc [] (List.suffix_refl [])).locallyIntegrableOn Ω.isOpen.measurableSet)
  | cons i I ih =>
    have hit : ∀ J, J.IsSuffix I → hasIntrinsicWordDeriv X Ω J f (jet J) :=
      fun J hJ => hi J (hJ.trans (List.suffix_cons i I))
    have hct : ∀ J, J.IsSuffix I → ContinuousOn (jet J) (Ω : Set (Fin N → ℝ)) :=
      fun J hJ => hc J (hJ.trans (List.suffix_cons i I))
    have hwt := ih hit hct
    apply (S.hasWeakWordDeriv_cons_iff X Ω hX hwt i).mpr
    obtain ⟨g, hg, hfirst⟩ := hi (i :: I) (List.suffix_refl _)
    have he := S.hasIntrinsicWordDeriv_unique Ω X I hg (hit I (List.suffix_refl _))
    have hfg := S.hasIntrinsicDeriv_congr_input Ω (X i) he hfirst
    have hw := S.hasWeakWordDeriv_of_intrinsic_derivative Ω (X i) (hX i)
      (jet I) (jet (i :: I)) (hct I (List.suffix_refl _))
      (hc (i :: I) (List.suffix_refl _)) hfg
    simpa only [hasWeakWordDeriv, wordTranspose] using hw

end RothschildStein.H3
