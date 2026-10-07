-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldDefs
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- Extending a smooth field independently of the added
coordinates preserves smoothness on the actual product domain. -/
theorem contDiffOn_paddingBaseField {n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (paddingBaseField (d := d) X)
      ((paddingBaseCLM n d) ⁻¹' Ω) := by
  have hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => X (paddingBaseCLM n d ξ))
      ((paddingBaseCLM n d) ⁻¹' Ω) :=
    hX.comp (paddingBaseCLM n d).contDiff.contDiffOn (fun _ hx => hx)
  have hj : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun ξ => paddingJoinCLM n d (X (paddingBaseCLM n d ξ), 0))
      ((paddingBaseCLM n d) ⁻¹' Ω) :=
    (paddingJoinCLM n d).contDiff.comp_contDiffOn (hp.prodMk contDiffOn_const)
  convert hj using 1
  funext ξ
  exact (paddingJoinCLM_apply n d _ _).symm

/-- The appended diffusion directions are globally smooth. -/
theorem contDiff_paddingDiffusionField {n d : ℕ} (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (paddingDiffusionField (n := n) j) := contDiff_const

/-- The entire drift-and-diffusion padded family is smooth
on the original-domain cylinder, with no global coefficient extension. -/
theorem contDiffOn_paddingVectorFields {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (paddingVectorFields (d := d) X i)
      ((paddingBaseCLM n d) ⁻¹' Ω) := by
  intro i
  refine Fin.cases ?_ (fun j => Fin.addCases ?_ ?_ j) i
  · rw [paddingVectorFields_zero]
    exact contDiffOn_paddingBaseField Ω (X 0) (hX 0)
  · intro j
    rw [paddingVectorFields_original]
    exact contDiffOn_paddingBaseField Ω (X j.succ) (hX j.succ)
  · intro j
    rw [paddingVectorFields_added]
    exact (contDiff_paddingDiffusionField j).contDiffOn

end RothschildStein.P1
