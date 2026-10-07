-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- Pulling a compact source back to its ball center preserves
continuity and compact support and gives the exact origin support buffer. -/
theorem translated_compact_source {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (z : Fin N → ℝ) (R : ℝ)
    (f : (Fin N → ℝ) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (quasiballDomain G ν z R : Set (Fin N → ℝ))) :
    Continuous (f ∘ G.mul z) ∧ HasCompactSupport (f ∘ G.mul z) ∧
      tsupport (f ∘ G.mul z) ⊆ (quasiballDomain G ν 0 R : Set (Fin N → ℝ)) := by
  refine ⟨hf.comp (G2.gaugeLeftTranslation G z).continuous,
    hc.comp_homeomorph (G2.gaugeLeftTranslation G z), ?_⟩
  have hp : tsupport (f ∘ G.mul z) ⊆ G.mul z ⁻¹' tsupport f := by
    apply closure_minimal
    · intro x hx
      exact subset_closure hx
    · exact (isClosed_tsupport f).preimage (G2.gaugeLeftTranslation G z).continuous
  rw [← quasiball_left_pullback G ν z R]
  exact hp.trans (preimage_mono hs)

end RothschildStein.H3
