-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectFreeness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- A formal basis detects injectivity of tangent evaluation. -/
theorem directPointEvaluation_injective_iff_basis_independent {ι : Type*} [Fintype ι] {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : TopologicalSpace.Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (x : Fin N → ℝ)
    (b : Module.Basis ι ℝ (formalSpan a s p)) :
    Function.Injective (directPointEvaluation (s := s) (p := p) Ω X hX x) ↔
      LinearIndependent ℝ (fun j => directPointEvaluation (s := s) (p := p) Ω X hX x (b j)) := by
  constructor
  · intro hi
    exact b.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hi)
  · intro hlin
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have he : ∑ j, b.equivFun f j • directPointEvaluation (s := s) (p := p) Ω X hX x (b j) = 0 := by
      have he := congrArg (directPointEvaluation (s := s) (p := p) Ω X hX x) (b.sum_equivFun f)
      simp only [map_sum,map_smul] at he
      exact he.trans hf
    have hz : ∀ j, b.equivFun f j = 0 := by
      apply (Fintype.linearIndependent_iffₛ.mp hlin) (b.equivFun f) 0
      simpa only [Pi.zero_apply,zero_smul,Finset.sum_const_zero] using he
    apply b.equivFun.injective
    rw [map_zero]
    exact funext hz
end RothschildStein.L1
