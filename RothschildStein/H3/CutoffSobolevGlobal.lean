-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SobolevMultiplication
public import RothschildStein.S.ZeroExtension
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3
variable {n m : ℕ}

/-- An interior compact cutoff sends local weighted Sobolev data
into the global weighted Sobolev class (BB Lemma 8.42, p. 371). -/
theorem cutoff_memSobolevX_global
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ)
    (hf : memSobolevX w X Ω k p f)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    memSobolevX w X ⊤ k p (fun x => f x * φ x) := by
  have hlocal := S.memSobolevX_mul_test w X Ω hX k p hp f hf φ
  let K : Compacts (Fin n → ℝ) := ⟨tsupport φ, φ.hasCompactSupport⟩
  have hK : (K : Set (Fin n → ℝ)) ⊆ Ω := φ.tsupport_subset
  have he : (Ω : Set (Fin n → ℝ)).indicator (fun x => f x * φ x) =
      fun x => f x * φ x := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simp [hx]
    · simp [hx, φ.zero_on_compl hx]
  have hs : ∀ᵐ x ∂volume, x ∈ (Ω : Set (Fin n → ℝ)) → x ∉ K →
      f x * φ x = 0 := by
    filter_upwards [] with x
    intro _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  refine ⟨?_, fun I hI => ?_⟩
  · have hm := (S.memLp_zeroExtension_iff Ω.isOpen.measurableSet _).mpr hlocal.1
    simpa only [he, Opens.coe_top, Measure.restrict_univ] using hm
  · obtain ⟨g, hg, hgp⟩ := hlocal.2 I hI
    refine ⟨(Ω : Set (Fin n → ℝ)).indicator g, ?_, ?_⟩
    · have hw := S.hasWeakWordDeriv_zeroExtension X ⊤ Ω (subset_univ _) K hK I
        (fun x => f x * φ x) g hg hs
      simpa only [he] using hw
    · have hm := (S.memLp_zeroExtension_iff Ω.isOpen.measurableSet g).mpr hgp
      simpa only [Opens.coe_top, Measure.restrict_univ] using hm

end RothschildStein.H3
