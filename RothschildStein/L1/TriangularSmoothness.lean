-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.TriangularProjection
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- Evaluation of a multivariate real polynomial is smooth. -/
theorem contDiff_polynomial_eval {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ : Fin N → ℝ => MvPolynomial.eval ξ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const (c := c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
        hp.mul (contDiff_apply ℝ ℝ i)

/-- The triangular lift `triangularLift` is smooth on the entire
ambient product domain whenever the original fields are smooth there. -/
theorem contDiffOn_triangularLift {q n m : ℕ} {Ω : Set (Fin n → ℝ)}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ) (i : Fin q) :
    ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (basePoint ⁻¹' Ω) := by
  have hbase : (⇑(P1.paddingBaseCLM n m) : (Fin (n + m) → ℝ) → (Fin n → ℝ)) =
      basePoint := funext (P1.paddingBaseCLM_apply n m)
  have hmap : MapsTo (P1.paddingBaseCLM n m) (basePoint ⁻¹' Ω) Ω := by
    intro ξ hξ
    simpa only [Set.mem_preimage, P1.paddingBaseCLM_apply] using hξ
  have hx : ContDiffOn ℝ (⊤ : ℕ∞) (X i ∘ basePoint (n := n) (m := m))
      (basePoint (n := n) (m := m) ⁻¹' Ω) := by
    simpa only [hbase] using (hX i).comp (P1.paddingBaseCLM n m).contDiff.contDiffOn
      hmap
  apply contDiffOn_pi.mpr
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simpa only [triangularLift, Fin.addCases_left, Function.comp_apply] using
      contDiffOn_pi.mp hx k
  · intro l
    simpa only [triangularLift, Fin.addCases_right] using
      (contDiff_polynomial_eval (P i l)).contDiffOn

end RothschildStein.L1
