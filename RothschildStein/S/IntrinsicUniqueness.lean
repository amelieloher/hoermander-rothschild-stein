-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasIntrinsicWordDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n q : ℕ}

/-- The intrinsic derivative respects equality of
its input on the open domain (BB p. 82; germ). -/
theorem hasIntrinsicDeriv_congr_input
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f h g : (Fin n → ℝ) → ℝ} (he : EqOn f h (Ω : Set (Fin n → ℝ)))
    (hg : hasIntrinsicDeriv Ω X f g) : hasIntrinsicDeriv Ω X h g := by
  intro x hx
  refine ⟨(hg x hx).1,fun γ hzero hγ hmem => ?_⟩
  have hd := (hg x hx).2 γ hzero hγ hmem
  apply hd.congr_of_eventuallyEq
  filter_upwards [hmem] with t ht
  exact (he ht).symm

/-- Intrinsic derivatives are unique pointwise because they agree along a common integral curve (BB p. 82). -/
theorem hasIntrinsicDeriv_unique
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    {f g h : (Fin n → ℝ) → ℝ}
    (hg : hasIntrinsicDeriv Ω X f g) (hh : hasIntrinsicDeriv Ω X f h) :
    EqOn g h (Ω : Set (Fin n → ℝ)) := by
  intro x hx
  obtain ⟨γ,hzero,hγ,hmem⟩ := (hg x hx).1
  exact ((hg x hx).2 γ hzero hγ hmem).unique ((hh x hx).2 γ hzero hγ hmem)

/-- All iterated intrinsic words are unique
pointwise, without a regularity hypothesis on intermediate choices
(BB p. 82; recursive uniqueness). -/
theorem hasIntrinsicWordDeriv_unique
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {f g h : (Fin n → ℝ) → ℝ}
    (hg : hasIntrinsicWordDeriv X Ω I f g)
    (hh : hasIntrinsicWordDeriv X Ω I f h) : EqOn g h (Ω : Set (Fin n → ℝ)) := by
  induction I generalizing g h with
  | nil => exact hg.trans hh.symm
  | cons i I ih =>
    obtain ⟨a,ha,hga⟩ := hg
    obtain ⟨b,hb,hgb⟩ := hh
    exact hasIntrinsicDeriv_unique Ω (X i)
      (hasIntrinsicDeriv_congr_input Ω (X i) (ih ha hb) hga) hgb

end RothschildStein.S
