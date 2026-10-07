-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalModelOrigin
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The actual canonical word field minus the constructed free model word. -/
def canonicalWordRemainder {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    {Ω : Set (Fin (freeDimension a s p) → ℝ)} {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) (I : List (Fin a))
    (q : (Fin (freeDimension a s p) → ℝ) × (Fin (freeDimension a s p) → ℝ)) :
    Fin (freeDimension a s p) → ℝ :=
  wordBracket (fun i => C.pullbackField q.1 (X i)) I q.2 - wordBracket D.fields I q.2

/-- Actual word remainders are jointly smooth
in the center and canonical coordinate on the same coefficient patch. -/
theorem canonicalWordRemainder_contDiffOn {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) (I : List (Fin a)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordRemainder D X C I)
      (ball x C.radius ×ˢ ball 0 C.radius) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞) (wordBracket D.fields I) := by
    rw [FreeModelData.fields, wordBracket_modelGenerators]
    exact contDiff_modelField _ _
  exact (C.pulled_wordBracket_contDiffOn_joint Ω.isOpen X hX I).sub
    (hm.comp contDiff_snd).contDiffOn

/-- Remainder values vanish on the zero section for retained words only. -/
theorem canonicalWordRemainder_zero {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    canonicalWordRemainder D X C I (η,0) = 0 :=
  canonical_wordBracket_remainder_zero D Ω X hX C η hη I hI
end RothschildStein.L1
