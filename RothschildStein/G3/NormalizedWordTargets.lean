-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EnumeratedWordProperties
public import RothschildStein.G3.FiniteLieFieldLinearity
public import RothschildStein.G3.FiniteLieFieldWords
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- The formal normalized target for one coefficient per retained word. -/
def normalizedWordTarget {a s : ℕ} {p : Fin a → ℕ+}
    (b : List (Fin a) → ℝ) : formalSpan a s p :=
  ((correctionWordEnumeration a s p s).map (fun I => b I • wordLieElement I)).sum

/-- A numerical target budget depending only on the finite word carrier. -/
def normalizedWordTargetBudget (a s : ℕ) (p : Fin a → ℕ+) : ℝ :=
  ((correctionWordEnumeration a s p s).map
    (fun I => ‖(wordLieElement I : formalSpan a s p)‖)).sum

/-- Coefficient bounds give the input-domain norm budget used by the analytic provider. -/
theorem norm_normalizedWordTarget_le {a s : ℕ} {p : Fin a → ℕ+}
    (b : List (Fin a) → ℝ)
    (hb : ∀ I ∈ correctionWordEnumeration a s p s, |b I| ≤ 1) :
    ‖normalizedWordTarget (s := s) (p := p) b‖ ≤ normalizedWordTargetBudget a s p := by
  let W := correctionWordEnumeration a s p s
  change ‖(W.map (fun I => b I • (wordLieElement I : formalSpan a s p))).sum‖ ≤
    (W.map (fun I => ‖(wordLieElement I : formalSpan a s p)‖)).sum
  have h : ∀ I ∈ W, ‖b I • (wordLieElement I : formalSpan a s p)‖ ≤
      ‖(wordLieElement I : formalSpan a s p)‖ := by
    intro I hI
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hb I hI) (norm_nonneg _)).trans_eq (one_mul _)
  revert h
  induction W with
  | nil => intro h; simp
  | cons I W ih =>
    intro h
    simp only [List.map_cons,List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h I List.mem_cons_self)
      (ih (fun J hJ => h J (List.mem_cons_of_mem I hJ))))
end RothschildStein.G3
