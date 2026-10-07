-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakToIntrinsic
public import RothschildStein.S.WeakDeriv
public import RothschildStein.Definitions.hasIntrinsicWordDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- A one-letter weak derivative depends only on its actual
field, so the single-field estimate applies to every alphabet index
(BB Def 2.1, p. 67; alphabet adapter). -/
theorem hasWeakWordDeriv_singleton_reindex
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin q)
    (f g : (Fin n → ℝ) → ℝ)
    (h : hasWeakWordDeriv X Ω [i] f g) :
    hasWeakWordDeriv (fun _ : Fin 1 => X i) Ω [0] f g := by
  simpa only [hasWeakWordDeriv,wordTranspose] using h

/-- Continuous weak word data provide the exact
iterated intrinsic derivative for every word. Subwords ensure
that all required suffixes are present; ordinary length drives the
induction, independently of weights (BB pp. 87–90). -/
theorem hasIntrinsicWordDeriv_of_continuous_weak_subwords
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J,J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    (hc : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ))) :
    hasIntrinsicWordDeriv X Ω I f (jet I) := by
  induction I with
  | nil =>
    change EqOn (jet []) f (Ω : Set (Fin n → ℝ))
    rw [hzero]
    exact fun _ _ => rfl
  | cons i I ih =>
    have hwt : ∀ J,J.Sublist I → hasWeakWordDeriv X Ω J f (jet J) :=
      fun J hJ => hw J (hJ.cons i)
    have hct : ∀ J,J.Sublist I → ContinuousOn (jet J) (Ω : Set (Fin n → ℝ)) :=
      fun J hJ => hc J (hJ.cons i)
    refine ⟨jet I,ih hwt hct,?_⟩
    have hfirst := (hasWeakWordDeriv_cons_iff X Ω hX (hwt I (List.Sublist.refl I)) i).mp
      (hw (i :: I) (List.Sublist.refl _))
    exact hasIntrinsicDeriv_of_continuous_weak_derivative Ω (X i) (hX i) (jet I) (jet (i :: I))
      (hct I (List.Sublist.refl I)) (hc (i :: I) (List.Sublist.refl _))
      (hasWeakWordDeriv_singleton_reindex Ω X i _ _ hfirst)

end RothschildStein.S
