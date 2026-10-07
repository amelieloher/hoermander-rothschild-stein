-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingHolderSlice
public import RothschildStein.S.IntrinsicCurveExistence
public import RothschildStein.Definitions.hasIntrinsicWordDeriv
public import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.P1

/-- Every intrinsic derivative along an original padded
field restricts to the same intrinsic derivative on a fixed fiber. -/
theorem hasIntrinsicDeriv_padding_slice {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (v g : (Fin (n + d) → ℝ) → ℝ)
    (hg : hasIntrinsicDeriv (P2.cylinder Ω J) (paddingBaseField (d := d) X) v g)
    (z : Fin d → ℝ) (hz : z ∈ (J : Set (Fin d → ℝ))) :
    hasIntrinsicDeriv Ω X (fun x => v (joinPoint x z)) (fun x => g (joinPoint x z)) := by
  intro x hx
  refine ⟨S.exists_intrinsic_integral_curve Ω X hX hx, ?_⟩
  intro γ hγ0 hγ hm
  let β : ℝ → (Fin (n + d) → ℝ) := fun t => joinPoint (γ t) z
  have hb0 : β 0 = joinPoint x z := by simp only [β, hγ0]
  have hb : IsIntegralCurveAt β (fun _ => paddingBaseField (d := d) X) 0 := by
    filter_upwards [hγ] with t ht
    have hd := (paddingJoinCLM n d).hasFDerivAt.comp_hasDerivAt t
      (ht.prodMk (hasDerivAt_const t z))
    have he : paddingBaseField (d := d) X (β t) =
        paddingJoinCLM n d (X (γ t), 0) := by
      simp only [paddingBaseField, β, paddingBaseCLM_join, paddingJoinCLM_apply]
    rw [← he] at hd
    simpa only [β, Function.comp_def, paddingJoinCLM_apply] using hd
  have hbm : ∀ᶠ t in 𝓝 (0 : ℝ), β t ∈ (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) := by
    filter_upwards [hm] with t ht
    exact P2.joinPoint_mem_cylinder.mpr ⟨ht, hz⟩
  exact (hg (joinPoint x z) (P2.joinPoint_mem_cylinder.mpr ⟨hx, hz⟩)).2 β hb0 hb hbm

/-- All intrinsic words in the original fields restrict
unchanged to a fixed fiber, including the pointwise empty-word predicate. -/
theorem hasIntrinsicWordDeriv_padding_slice {k n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin k)) (v g : (Fin (n + d) → ℝ) → ℝ)
    (hg : hasIntrinsicWordDeriv (fun i => paddingBaseField (d := d) (X i))
      (P2.cylinder Ω J) I v g)
    (z : Fin d → ℝ) (hz : z ∈ (J : Set (Fin d → ℝ))) :
    hasIntrinsicWordDeriv X Ω I (fun x => v (joinPoint x z)) (fun x => g (joinPoint x z)) := by
  induction I generalizing g with
  | nil =>
      intro x hx
      exact hg (P2.joinPoint_mem_cylinder.mpr ⟨hx, hz⟩)
  | cons i I ih =>
      obtain ⟨h, hI, hi⟩ := hg
      exact ⟨fun x => h (joinPoint x z), ih h hI,
        hasIntrinsicDeriv_padding_slice Ω J (X i) (hX i) h g hi z hz⟩

end RothschildStein.P1
