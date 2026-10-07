-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.NormalizedWordTargets
public import RothschildStein.G3.RetainedLieDilation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Weighted dilation, as a linear map on the retained formal carrier. -/
def retainedDilationLinear {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ) :
    formalSpan a s p →ₗ[ℝ] formalSpan a s p where
  toFun := retainedLieDilation t
  map_add' f g := by
    apply Subtype.ext
    exact (dilationLinearMap t).map_add f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (dilationLinearMap t).map_smul c f.val

/-- Each retained nested word has its prescribed weighted scaling. -/
theorem retainedLieDilation_word {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (I : List (Fin a)) :
    retainedLieDilation t (wordLieElement I : formalSpan a s p) =
      t^wordWeight p I • (wordLieElement I : formalSpan a s p) := by
  apply Subtype.ext
  exact finiteDilate_truncatedBracket t I

/-- Restoring the small parameter gives precisely the source weighted coefficients. -/
theorem retainedLieDilation_normalizedWordTarget {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (b : List (Fin a) → ℝ) :
    retainedLieDilation t (normalizedWordTarget (s := s) (p := p) b) =
      normalizedWordTarget (s := s) (p := p) (fun I => t^wordWeight p I * b I) := by
  let W := correctionWordEnumeration a s p s
  change retainedDilationLinear t ((W.map (fun I => b I • wordLieElement I)).sum) =
    (W.map (fun I => (t^wordWeight p I * b I) • wordLieElement I)).sum
  have hmap : ∀ U : List (formalSpan a s p), retainedDilationLinear t U.sum =
      (U.map (retainedDilationLinear t)).sum := by
    intro U
    induction U with
    | nil => exact (retainedDilationLinear t).map_zero
    | cons u U ih => simp only [List.sum_cons,List.map_cons,map_add,ih]
  rw [hmap,List.map_map]
  congr 1
  apply List.map_congr_left
  intro I _
  rw [Function.comp_apply,map_smul]
  change b I • retainedLieDilation t (wordLieElement I) = _
  rw [retainedLieDilation_word,smul_smul,mul_comm]
end RothschildStein.G3
