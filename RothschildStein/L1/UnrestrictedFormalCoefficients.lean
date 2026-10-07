-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FormalWordCoefficients
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1
open G3

/-- Formal combinations are surjective even when some generator weights
exceed the cutoff, as required for the drift at cutoff one. -/
theorem formalWordCoefficientMap_surjective_unrestricted {a s : ℕ} {p : Fin a → ℕ+} :
    Function.Surjective (formalWordCoefficientMap (a := a) (s := s) (p := p)) := by
  classical
  have h : ∀ f : WordCoefficients a s p, f ∈ formalSpan a s p →
      ∃ c : BoundedWord a s p → ℝ, (formalWordCoefficientMap c).val = f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨I,_,hI,rfl⟩ := hf
      refine ⟨Pi.single (boundedWord p I hI) 1,?_⟩
      rw [formalWordCoefficientMap_single]
      rfl
    | zero => exact ⟨0,by rw [map_zero]; rfl⟩
    | add f g _ _ hf hg =>
      obtain ⟨c,hc⟩ := hf
      obtain ⟨d,hd⟩ := hg
      exact ⟨c+d,by rw [map_add]; change (formalWordCoefficientMap c).val + (formalWordCoefficientMap d).val = _; rw [hc,hd]⟩
    | smul r f _ hf =>
      obtain ⟨c,hc⟩ := hf
      exact ⟨r • c,by rw [map_smul]; change r • (formalWordCoefficientMap c).val = _; rw [hc]⟩
  intro f
  obtain ⟨c,hc⟩ := h f.val f.property
  exact ⟨c,Subtype.ext hc⟩
end RothschildStein.L1
