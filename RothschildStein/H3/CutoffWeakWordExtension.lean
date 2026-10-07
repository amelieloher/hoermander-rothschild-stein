-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace

/-- An interior compact cutoff product's certified local word jet
extends to a global weak word jet by zero extension. -/
theorem cutoff_weak_word_extension {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin m))
    (u g : (Fin n → ℝ) → ℝ) (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hg : hasWeakWordDeriv X Ω I (fun x => u x * φ x) g) :
    hasWeakWordDeriv X ⊤ I (fun x => u x * φ x)
      ((Ω : Set (Fin n → ℝ)).indicator g) := by
  let K : Compacts (Fin n → ℝ) := ⟨tsupport φ, φ.hasCompactSupport⟩
  have he : (Ω : Set (Fin n → ℝ)).indicator (fun x => u x * φ x) =
      fun x => u x * φ x := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simp [hx]
    · simp [hx, φ.zero_on_compl hx]
  have hs : ∀ᵐ x ∂volume, x ∈ (Ω : Set (Fin n → ℝ)) → x ∉ K → u x * φ x = 0 := by
    filter_upwards [] with x
    intro _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hw := S.hasWeakWordDeriv_zeroExtension X ⊤ Ω (subset_univ _) K
    φ.tsupport_subset I (fun x => u x * φ x) g hg hs
  simpa only [he] using hw

end RothschildStein.H3
