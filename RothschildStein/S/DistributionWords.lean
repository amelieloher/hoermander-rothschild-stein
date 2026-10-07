-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestOperators
public import RothschildStein.S.WeakDeriv
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology Distributions CompactConvergenceCLM
namespace RothschildStein.S
variable {n m : ℕ}

/-- Distributional words are continuous transposes of test words
(BB p. 68). -/
def distributionWordCLM (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) :
    Distribution Ω ℝ (⊤ : ℕ∞) →L[ℝ] Distribution Ω ℝ (⊤ : ℕ∞) :=
  (wordTransposeCLM Ω X hX I).precompCompactConvergenceCLM ℝ

/-- Evaluation formula for distributional words (BB p. 68). -/
theorem distributionWordCLM_apply (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    distributionWordCLM Ω X hX I T φ = T (wordTransposeTest Ω X hX I φ) := by
  change T (wordTransposeCLM Ω X hX I φ) = _
  rw [wordTransposeCLM_apply]

/-- weak words agree with transposition of regular distributions
(BB Def. 2.1, pp. 67–68). -/
theorem distributionWord_ofFun_eq (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (f g : (Fin n → ℝ) → ℝ)
    (h : hasWeakWordDeriv X Ω I f g) :
    distributionWordCLM Ω X hX I (Distribution.ofFun Ω f volume (⊤ : ℕ∞)) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) := by
  ext φ
  rw [distributionWordCLM_apply, Distribution.ofFun_apply h.1, Distribution.ofFun_apply h.2.1]
  have hfzero : ∀ x, x ∉ (Ω : Set (Fin n → ℝ)) →
      wordTransposeTest Ω X hX I φ x * f x = 0 := by
    intro x hx
    simp [(wordTransposeTest Ω X hX I φ).zero_on_compl hx]
  have hgzero : ∀ x, x ∉ (Ω : Set (Fin n → ℝ)) → φ x * g x = 0 := by
    intro x hx
    simp [φ.zero_on_compl hx]
  simp only [smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hgzero]
  rw [wordTransposeTest_apply]
  simpa only [mul_comm] using (h.2.2 φ).symm

end RothschildStein.S
