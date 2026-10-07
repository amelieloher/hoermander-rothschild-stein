-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffSobolevGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- A compact cutoff product has identical global and local weak
word norms, including at infinite exponent (BB Lemma 8.42, p. 371). -/
theorem cutoff_weakNorm_global_eq_local {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (u g : (Fin n → ℝ) → ℝ) (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hg : hasWeakWordDeriv X Ω I (fun x => u x * φ x) g) :
    weakWordENorm X ⊤ I p (fun x => u x * φ x) =
      weakWordENorm X Ω I p (fun x => u x * φ x) := by
  let K : Compacts (Fin n → ℝ) := ⟨tsupport φ, φ.hasCompactSupport⟩
  have he : (Ω : Set (Fin n → ℝ)).indicator (fun x => u x * φ x) =
      fun x => u x * φ x := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simp [hx]
    · simp [hx, φ.zero_on_compl hx]
  have hs : ∀ᵐ x ∂volume, x ∈ (Ω : Set (Fin n → ℝ)) → x ∉ K →
      u x * φ x = 0 := by
    filter_upwards [] with x
    intro _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hw := S.hasWeakWordDeriv_zeroExtension X ⊤ Ω (subset_univ _) K
    φ.tsupport_subset I (fun x => u x * φ x) g hg hs
  rw [he] at hw
  rw [S.weakWordENorm_eq X ⊤ I p _ _ hw,
    S.weakWordENorm_eq X Ω I p _ g hg]
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    S.eLpNorm_zeroExtension (p := p) Ω.isOpen.measurableSet g

end RothschildStein.H3
