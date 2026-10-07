-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorInvariance
public import RothschildStein.S.ClassicalWords
public import RothschildStein.H3.SmoothGaugeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace
variable {N m : ℕ} (G : HomogeneousGroup N)

/-- Left invariance for an arbitrary classical word. This transfers
all radial cutoff bounds to every center with the same constants. -/
theorem wordDerivative_leftTranslation
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    (I : List (Fin m)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Fin N → ℝ) :
    wordDerivative X I (f ∘ G.mul y) = (wordDerivative X I f) ∘ G.mul y := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    simp only [wordDerivative, ih]
    apply (hleft i).operator
    exact contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ X
      (fun i => (hX i).contDiffOn) I f hf.contDiffOn)

/-- The translated smooth gauge cutoff satisfies the word identity
without any supplied smoothness hypothesis on the scalar radial composition. -/
theorem wordDerivative_smoothQuasiballCutoff
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    (I : List (Fin m)) (x₀ : Fin N → ℝ)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    wordDerivative X I (smoothQuasiballCutoff G ν x₀ t s) =
      (wordDerivative X I (quasiballProfile t s ∘ ν)) ∘ G.mul (G.inv x₀) :=
  wordDerivative_leftTranslation G X hX hleft I _
    (contDiff_radial_quasiballProfile ν hν ht hts) _

end RothschildStein.H3
