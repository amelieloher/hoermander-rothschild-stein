-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFieldLinearity
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- A finite Lie field's spatial jet is bounded by the finite sum of
its absolute coefficients times the corresponding actual word-field jets
(BB Lemma 9.22, pp. 413–414). -/
theorem norm_iteratedFDeriv_finiteLieField_le {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p)
    (r : ℕ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ r (finiteLieField D X f) x‖ ≤
      ∑ j, |D.basis.equivFun f j| *
        ‖iteratedFDeriv ℝ r (wordBracket X (modelBasisWord D j)) x‖ := by
  have hj : ∀ j : Fin (freeDimension a s p),
      ContDiffAt ℝ r (wordBracket X (modelBasisWord D j)) x := by
    intro j
    exact ((G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)).contDiffAt
      (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  unfold finiteLieField
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hj j).const_smul _)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  change ‖iteratedFDeriv ℝ r
    (D.basis.equivFun f j • wordBracket X (modelBasisWord D j)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hj j), norm_smul, Real.norm_eq_abs]
end RothschildStein.G3
