-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SobolevMultiplication
public import RothschildStein.S.ZeroExtension
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3
variable {N q : ℕ}

/-- A compactly supported Sobolev input inside an open set is a
global Sobolev input, with actual zero extensions of its weak jets. The
proved S zero-extension theorem supplies every word identity (BB Cor 2.10). -/
theorem memSobolevX_globalize_of_compact_support (w : Fin q → ℕ+)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (Ω : Opens (Fin N → ℝ))
    {k : ℕ} {p : ℝ≥0∞} {f : (Fin N → ℝ) → ℝ}
    (hf : memSobolevX w X Ω k p f) (hcf : HasCompactSupport f)
    (hs : tsupport f ⊆ (Ω : Set (Fin N → ℝ))) : memSobolevX w X ⊤ k p f := by
  classical
  let K : Compacts (Fin N → ℝ) := ⟨tsupport f, hcf.isCompact⟩
  have hi : (Ω : Set (Fin N → ℝ)).indicator f = f := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin N → ℝ))
    · exact indicator_of_mem hx f
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm
  have hglob : memSobolevX w X ⊤ k p ((Ω : Set (Fin N → ℝ)).indicator f) := by
    refine ⟨?_, ?_⟩
    · have hlp := (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).mpr hf.1
      simpa only [Opens.coe_top, Measure.restrict_univ] using hlp
    · intro I hI
      obtain ⟨g, hg, hgp⟩ := hf.2 I hI
      refine ⟨(Ω : Set (Fin N → ℝ)).indicator g, ?_, ?_⟩
      · exact S.hasWeakWordDeriv_zeroExtension X ⊤ Ω (subset_univ _) K hs I f g hg
          (Eventually.of_forall fun x _ hx => image_eq_zero_of_notMem_tsupport hx)
      · have hlp := (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).mpr hgp
        simpa only [Opens.coe_top, Measure.restrict_univ] using hlp
  rw [hi] at hglob
  exact hglob

end RothschildStein.H3
