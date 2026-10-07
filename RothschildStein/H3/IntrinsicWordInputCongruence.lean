-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicNormRepresentatives
public import RothschildStein.Definitions.memHolderX

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Iterated intrinsic derivatives depend only on the input
on the chosen open domain. The intermediate representatives are retained. -/
theorem intrinsic_word_congr_input {N m : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (I : List (Fin m)) {u v g : (Fin N → ℝ) → ℝ}
    (he : EqOn u v (U : Set (Fin N → ℝ)))
    (hg : hasIntrinsicWordDeriv X U I u g) : hasIntrinsicWordDeriv X U I v g := by
  induction I generalizing g with
  | nil => exact hg.trans he
  | cons i I ih =>
    obtain ⟨h, hh, hder⟩ := hg
    exact ⟨h, ih hh, hder⟩

/-- The exact fixed intrinsic infimum norm depends only on
values of its input on the domain. -/
theorem intrinsic_word_norm_congr_input {N m : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (U : Opens (Fin N → ℝ))
    (I : List (Fin m)) (α : ℝ) {u v : (Fin N → ℝ) → ℝ}
    (he : EqOn u v (U : Set (Fin N → ℝ))) :
    intrinsicWordENorm X d U I α u = intrinsicWordENorm X d U I α v := by
  unfold intrinsicWordENorm
  congr 1
  ext r
  constructor
  · rintro ⟨g, hg, hr⟩
    exact ⟨g, intrinsic_word_congr_input X U I he hg, hr⟩
  · rintro ⟨g, hg, hr⟩
    exact ⟨g, intrinsic_word_congr_input X U I he.symm hg, hr⟩

end RothschildStein.H3
