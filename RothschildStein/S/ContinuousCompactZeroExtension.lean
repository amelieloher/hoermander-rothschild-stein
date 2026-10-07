-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ContinuousTestProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
namespace RothschildStein.S
variable {n : ℕ}

/-- A continuous function supported in an
interior compact set of its local domain has a globally continuous
compact zero extension, with the same support bound. Exterior
values of the original input are unrestricted
(BB Thm 2.20, p. 86; local compact-support adapter). -/
theorem continuous_compact_zeroExtension_of_local_support
    (Ω : Opens (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hz : ∀ x ∈ (Ω : Set (Fin n → ℝ)) \ K,f x = 0) :
    Continuous ((Ω : Set (Fin n → ℝ)).indicator f) ∧
      HasCompactSupport ((Ω : Set (Fin n → ℝ)).indicator f) ∧
      tsupport ((Ω : Set (Fin n → ℝ)).indicator f) ⊆ K := by
  obtain ⟨χ,W,hW,hKW,hWΩ,hχ⟩ := exists_test_plateau Ω ⟨K,hK⟩ hKΩ
  have he : (Ω : Set (Fin n → ℝ)).indicator f = fun x => f x*χ x := by
    funext x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · rw [indicator_of_mem hx]
      by_cases hk : x ∈ K
      · have hc : χ x = 1 := hχ (hKW hk)
        rw [hc,mul_one]
      · rw [hz x ⟨hx,hk⟩,zero_mul]
    · rw [indicator_of_notMem hx]
      simpa using congrArg (fun a : ℝ => f x * a) (χ.zero_on_compl hx).symm
  have hs : Function.support ((Ω : Set (Fin n → ℝ)).indicator f) ⊆ K := by
    intro x hx
    by_contra hk
    apply hx
    by_cases ho : x ∈ (Ω : Set (Fin n → ℝ))
    · rw [indicator_of_mem ho]
      exact hz x ⟨ho,hk⟩
    · exact indicator_of_notMem ho f
  have ht : tsupport ((Ω : Set (Fin n → ℝ)).indicator f) ⊆ K :=
    closure_minimal hs hK.isClosed
  refine ⟨?_,hK.of_isClosed_subset isClosed_closure ht,ht⟩
  rw [he]
  exact continuous_mul_test_of_continuousOn Ω hf χ

end RothschildStein.S
