-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LinearFieldCoefficientApply
public import RothschildStein.G3.FiniteLieFields
public import RothschildStein.G1.BracketAlgebra

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G1
open G3

/-- The genuine finite Lie flow has the coefficient derivative
required by the retained-log endpoint lemma. This identity is derived
from the actual finite Lie ODE, not postulated for the endpoint. -/
theorem finite_lie_timeOne_coefficient_derivative {a s n : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {A : Set (Fin (freeDimension a s p) → ℝ)} (hA : IsOpen A) (hz : 0 ∈ A)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((A ×ˢ U) ×ˢ Ioo (-2 : ℝ) 2))
    (hODE : ∀ f : formalSpan a s p, D.basis.equivFun f ∈ A → ∀ x ∈ U,
      Φ ((D.basis.equivFun f, x), 0) = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun v => Φ ((D.basis.equivFun f, x), v))
          (finiteLieField D X f (Φ ((D.basis.equivFun f, x), t))) t ∧
        Φ ((D.basis.equivFun f, x), t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) (f : formalSpan a s p) :
    fderiv ℝ (fun z => Φ ((z, x), 1)) 0 (D.basis.equivFun f) = finiteLieField D X f x := by
  let W := fun j => wordBracket X (modelBasisWord D j)
  have hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω :=
    fun j => wordBracket_contDiffOn hΩ X hX (modelBasisWord D j)
  have hlin : ∀ q ∈ A ×ˢ U, Φ (q, 0) = q.2 ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun v => Φ (q, v)) (∑ j, q.1 j • W j (Φ (q, t))) t ∧ Φ (q, t) ∈ Ω := by
    intro q hq
    have hback : D.basis.equivFun (D.basis.equivFun.symm q.1) = q.1 :=
      D.basis.equivFun.apply_symm_apply q.1
    have hh := hODE (D.basis.equivFun.symm q.1) (by rw [hback]; exact hq.1) q.2 hq.2
    simpa only [finiteLieField, hback, W] using hh
  exact linear_field_timeOne_coefficient_apply hA hΩ hU hUΩ W hW hz (by norm_num)
    Φ hΦ.continuousOn hlin hx (D.basis.equivFun f)

end RothschildStein.G1
