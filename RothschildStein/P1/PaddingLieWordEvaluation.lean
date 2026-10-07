-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingLieWordDefs
public import RothschildStein.P1.PaddingVectorDerivative
public import Hormander.F.WordLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1

private theorem lieWordEval_eq_interface {q n : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (w : Hormander.Interface.LieWord q) :
    Hormander.lieWordEval X w = Hormander.Interface.LieWord.eval X w := by
  induction w with
  | generator i => rfl
  | bracket p r hp hr => simp only [Hormander.lieWordEval, Hormander.Interface.LieWord.eval, hp, hr]

/-- Every original Lie word evaluates in the padded system
as its original value with zero added components. The coefficient
smoothness and equality are needed only on the original open domain. -/
theorem lieWordEval_paddingLieWord {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∀ w : Hormander.Interface.LieWord q,
      EqOn (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord w))
        (paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X w))
        ((paddingBaseCLM n d) ⁻¹' Ω) := by
  let U := (paddingBaseCLM n d) ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (paddingBaseCLM n d).continuous
  intro w
  induction w with
  | generator i =>
      intro ξ hξ
      simp only [paddingLieWord, Hormander.Interface.LieWord.eval,
        paddingVectorFields_generatorIndex]
  | bracket p r hp hr =>
      intro ξ hξ
      have hep : (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord p))
          =ᶠ[𝓝 ξ] paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X p) := by
        filter_upwards [hU.mem_nhds hξ] with y hy
        exact hp hy
      have her : (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord r))
          =ᶠ[𝓝 ξ] paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X r) := by
        filter_upwards [hU.mem_nhds hξ] with y hy
        exact hr hy
      have hcp := Hormander.F.lieWordEval_contDiffOn hΩ X hX p
      have hcr := Hormander.F.lieWordEval_contDiffOn hΩ X hX r
      rw [lieWordEval_eq_interface X p] at hcp
      rw [lieWordEval_eq_interface X r] at hcr
      have hdp := (hcp.contDiffAt (hΩ.mem_nhds hξ)).differentiableAt (by simp)
      have hdr := (hcr.contDiffAt (hΩ.mem_nhds hξ)).differentiableAt (by simp)
      change VectorField.lieBracket ℝ
        (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord p))
        (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord r)) ξ =
          paddingBaseField (d := d) (VectorField.lieBracket ℝ
            (Hormander.Interface.LieWord.eval X p) (Hormander.Interface.LieWord.eval X r)) ξ
      have hb := lieBracket_paddingBaseField (d := d)
        (Hormander.Interface.LieWord.eval X p) (Hormander.Interface.LieWord.eval X r) ξ hdp hdr
      refine Eq.trans ?_ hb
      change
        fderiv ℝ (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord r)) ξ
          (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord p) ξ) -
        fderiv ℝ (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord p)) ξ
          (Hormander.Interface.LieWord.eval (paddingVectorFields (d := d) X) (paddingLieWord r) ξ) =
        fderiv ℝ (paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X r)) ξ
          (paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X p) ξ) -
        fderiv ℝ (paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X p)) ξ
          (paddingBaseField (d := d) (Hormander.Interface.LieWord.eval X r) ξ)
      rw [hep.fderiv_eq, her.fderiv_eq, hp hξ, hr hξ]

end RothschildStein.P1
