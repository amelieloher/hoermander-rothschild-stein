-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakIntrinsicWords
public import RothschildStein.S.IntrinsicUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- Continuous intrinsic
subword data give the same weak word representatives. The hypothesis
is the full single-field intrinsic-to-weak theorem on any open domain,
without bracket or nonvanishing assumptions (BB pp. 87–90). -/
theorem hasWeakWordDeriv_of_intrinsicToWeak
    (hReverse : ∀ (V : Opens (Fin n → ℝ))
      (Y : (Fin n → ℝ) → (Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) Y (V : Set (Fin n → ℝ)) →
      ∀ f g : (Fin n → ℝ) → ℝ,
      ContinuousOn f (V : Set (Fin n → ℝ)) →
      ContinuousOn g (V : Set (Fin n → ℝ)) →
      hasIntrinsicDeriv V Y f g →
      hasWeakWordDeriv (fun _ : Fin 1 => Y) V [0] f g)
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ J,J.Sublist I → hasIntrinsicWordDeriv X Ω J f (jet J))
    (hc : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ))) :
    hasWeakWordDeriv X Ω I f (jet I) := by
  induction I with
  | nil =>
    rw [hzero]
    exact hasWeakWordDeriv_nil X Ω
      (by simpa only [hzero] using
        (hc [] (List.Sublist.refl [])).locallyIntegrableOn Ω.isOpen.measurableSet)
  | cons i I ih =>
    have hit : ∀ J,J.Sublist I → hasIntrinsicWordDeriv X Ω J f (jet J) :=
      fun J hJ => hi J (hJ.cons i)
    have hct : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ)) :=
      fun J hJ => hc J (hJ.cons i)
    have hwt := ih hit hct
    apply (hasWeakWordDeriv_cons_iff X Ω hX hwt i).mpr
    obtain ⟨g,hg,hfirst⟩ := hi (i :: I) (List.Sublist.refl _)
    have he := hasIntrinsicWordDeriv_unique Ω X I hg (hit I (List.Sublist.refl _))
    have hf := hasIntrinsicDeriv_congr_input Ω (X i) he hfirst
    have hw := hReverse Ω (X i) (hX i) (jet I) (jet (i :: I))
      (hct I (List.Sublist.refl _)) (hc (i :: I) (List.Sublist.refl _)) hf
    simpa only [hasWeakWordDeriv,wordTranspose] using hw

end RothschildStein.S
