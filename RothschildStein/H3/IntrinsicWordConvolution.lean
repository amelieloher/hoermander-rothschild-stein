-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicConvolution
public import RothschildStein.Definitions.wordDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Iterated invariant derivatives commute pointwise with
smooth compact group convolution for compact continuous intrinsic jets.
The fixed recursive word predicate supplies the intermediate derivative;
uniqueness identifies it with the declared jet. -/
theorem wordDerivative_convolution_of_compact_intrinsic
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hleft : ∀ i, G2.IsLeftInvariantField G (X i))
    {ψ : (Fin N → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) (I : List (Fin q)) (f : (Fin N → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin N → ℝ) → ℝ) (hzero : jet [] = f)
    (hi : ∀ J, J.IsSuffix I → hasIntrinsicWordDeriv X ⊤ J f (jet J))
    (hc : ∀ J, J.IsSuffix I → Continuous (jet J))
    (hs : ∀ J, J.IsSuffix I → HasCompactSupport (jet J)) :
    wordDerivative X I (G2.groupConvolution G ψ f) = G2.groupConvolution G ψ (jet I) := by
  induction I with
  | nil => simp only [wordDerivative, hzero]
  | cons i I ih =>
    have hit : ∀ J, J.IsSuffix I → hasIntrinsicWordDeriv X ⊤ J f (jet J) :=
      fun J hJ => hi J (hJ.trans (List.suffix_cons i I))
    have hct : ∀ J, J.IsSuffix I → Continuous (jet J) := fun J hJ => hc J (hJ.trans (List.suffix_cons i I))
    have hst : ∀ J, J.IsSuffix I → HasCompactSupport (jet J) := fun J hJ => hs J (hJ.trans (List.suffix_cons i I))
    have htail := ih hit hct hst
    obtain ⟨g, hg, hfirst⟩ := hi (i :: I) (List.suffix_refl _)
    have he := S.hasIntrinsicWordDeriv_unique ⊤ X I hg (hit I (List.suffix_refl _))
    have hfg := S.hasIntrinsicDeriv_congr_input ⊤ (X i) he hfirst
    change fieldDerivative (X i) (wordDerivative X I (G2.groupConvolution G ψ f)) = _
    rw [htail]
    exact fieldDerivative_convolution_of_compact_intrinsic G (X i) (hX i) (hleft i)
      hψ hcψ (hct I (List.suffix_refl _)) (hst I (List.suffix_refl _))
      (hc (i :: I) (List.suffix_refl _)) (hs (i :: I) (List.suffix_refl _)) hfg

end RothschildStein.H3
