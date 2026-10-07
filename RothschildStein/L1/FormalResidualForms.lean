-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WordJetResiduals
public import RothschildStein.L1.DirectEvaluation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The residual of a product of formal
commutators is multilinear in those commutators, before imposing a weight cutoff. -/
def formalResidualForm {a s N r : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : smoothOnFunctions Ω) (x : Fin N → ℝ) (c : List (Fin a) → ℝ) :
    MultilinearMap ℝ (fun _ : Fin r => formalSpan a s p) ℝ :=
  (wordJetResidual Ω X hX u x c).compMultilinearMap
    ((MultilinearMap.mkPiAlgebraFin ℝ r (MonoidAlgebra ℝ (FreeMonoid (Fin a)))).compLinearMap
      (fun _ => finitePolynomialLinear.comp (formalSpan a s p).subtype))

/-- The multilinear form is the actual prescribed-minus-realized residual
on the ordered product of untruncated associative representatives. -/
theorem formalResidualForm_apply {a s N r : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : smoothOnFunctions Ω) (x : Fin N → ℝ) (c : List (Fin a) → ℝ)
    (v : Fin r → formalSpan a s p) :
    formalResidualForm Ω X hX u x c v =
      wordJetResidual Ω X hX u x c (List.ofFn (fun i => finitePolynomialLinear (v i).val)).prod := by
  rfl
end RothschildStein.L1
