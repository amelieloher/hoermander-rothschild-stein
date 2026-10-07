-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalWordRemainder
public import RothschildStein.L1.AutomaticJetWeights
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The strict approximation weight for words beyond the cutoff is
automatic from nonpositive coefficient thresholds. It implies no value
vanishing at the origin. -/
theorem canonical_high_word_remainder_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (I : List (Fin a)) (hI : s < wordWeight p I) :
    fullFieldJetClass (ball 0 C.radius) D.weight (1 - (wordWeight p I : ℝ))
      (fun u => canonicalWordRemainder D X C I (η,u)) := by
  have harg : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : Fin (freeDimension a s p) → ℝ => (η,u)) (ball 0 C.radius) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hs := (canonicalWordRemainder_contDiffOn D Ω X hX C I).comp harg
    (fun u hu => ⟨hη,hu⟩)
  apply fullFieldJetClass_of_nonpos_thresholds _ D.weight _ _ hs
  intro j
  have hb : (D.weight j : ℝ) ≤ (s : ℝ) := by exact_mod_cast D.weight_bound j
  have hi : (s : ℝ) + 1 ≤ (wordWeight p I : ℝ) := by
    have hn : s + 1 ≤ wordWeight p I := hI
    exact_mod_cast hn
  linarith
end RothschildStein.L1
