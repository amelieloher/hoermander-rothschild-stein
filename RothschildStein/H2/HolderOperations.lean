-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderEstimates

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- The full Hölder norm is subadditive. -/
theorem boundedHolderNorm_add_le {δ : ℝ≥0} {G : Set X} {f g : X → ℝ} :
    boundedHolderNorm δ G (fun x => f x + g x) ≤ boundedHolderNorm δ G f + boundedHolderNorm δ G g := by
  have hs : holderSup G (fun x => f x + g x) ≤ holderSup G f + holderSup G g := by
    apply iSup_le
    intro x
    calc
      _ ≤ ENNReal.ofReal (|f x| + |g x|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |f x| + ENNReal.ofReal |g x| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add (le_iSup (fun y : G => ENNReal.ofReal |f y|) x)
        (le_iSup (fun y : G => ENNReal.ofReal |g y|) x)
  have hh : holderSemi δ G (fun x => f x + g x) ≤ holderSemi δ G f + holderSemi δ G g :=
    eHolderNorm_add_le
  calc
    _ ≤ (holderSup G f + holderSup G g) + (holderSemi δ G f + holderSemi δ G g) := add_le_add hs hh
    _ = _ := by unfold boundedHolderNorm; ac_rfl

/-- The bounded Hölder class is closed under addition. -/
theorem BoundedHolder.add {δ : ℝ≥0} {G : Set X} {f g : X → ℝ}
    (hf : BoundedHolder δ G f) (hg : BoundedHolder δ G g) :
    BoundedHolder δ G (fun x => f x + g x) :=
  boundedHolderNorm_add_le.trans_lt (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)

/-- Hölder norms depend only on values on their declared domain. -/
theorem boundedHolderNorm_congr {δ : ℝ≥0} {G : Set X} {f g : X → ℝ} (hfg : EqOn f g G) :
    boundedHolderNorm δ G f = boundedHolderNorm δ G g := by
  have he : (fun x : G => f x) = (fun x : G => g x) := funext fun x => hfg x.property
  unfold boundedHolderNorm holderSup holderSemi
  rw [he]
  congr 1
  apply iSup_congr
  intro x
  rw [hfg x.property]

/-- Restricting the input domain decreases its full Hölder norm. -/
theorem boundedHolderNorm_restrict {δ : ℝ≥0} {E G : Set X} {f : X → ℝ} (hEG : E ⊆ G) :
    boundedHolderNorm δ E f ≤ boundedHolderNorm δ G f := by
  have hs : holderSup E f ≤ holderSup G f := by
    apply iSup_le
    intro x
    exact le_iSup (fun y : G => ENNReal.ofReal |f y|) ⟨x, hEG x.property⟩
  have hh : holderSemi δ E f ≤ holderSemi δ G f := by
    by_cases hh : holderSemi δ G f = ⊤
    · rw [hh]
      exact le_top
    · have he := holderSemi_le_of_bound (δ := δ) (A := E)
        (H := (holderSemi δ G f).toReal) ENNReal.toReal_nonneg (by
          intro x hx y hy
          exact sub_le_holderSemi (lt_top_iff_ne_top.mpr hh) (hEG hx) (hEG hy))
      simpa only [ENNReal.ofReal_toReal hh] using he
  exact add_le_add hs hh

end RothschildStein.H2
