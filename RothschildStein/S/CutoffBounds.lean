-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MultiplicationBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n m : ℕ}

/-- The maximum L∞ norm of the weighted cutoff words (BB p. 73). -/
def cutoffWordENorm (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (k : ℕ) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : ℝ≥0∞ :=
  (wordFamily w k).sup (fun J =>
    eLpNorm (wordDerivative X J φ) ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))))

/-- Compact smooth cutoff words have a finite maximum L∞ norm
(BB p. 73). -/
theorem cutoffWordENorm_lt_top (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : cutoffWordENorm w X Ω k φ < ⊤ := by
  classical
  unfold cutoffWordENorm
  apply (Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)).mpr
  intro J _
  exact (wordDerivativeTest Ω X hX J φ).memLp_top.eLpNorm_lt_top

/-- The quantitative cutoff estimate with all weak representatives
provided by Sobolev membership (BB p. 73). -/
theorem sobolevXENorm_mul_test_le (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ)
    (hf : memSobolevX w X Ω k p f) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    sobolevXENorm w X Ω k p (fun x => f x * φ x) ≤
      (2 ^ k * (wordFamily w k).card : ℕ) * cutoffWordENorm w X Ω k φ *
        sobolevXENorm w X Ω k p f := by
  classical
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  let P := fun I => ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X Ω I f g ∧ MemLp g p μ
  let F : List (Fin m) → (Fin n → ℝ) → ℝ := fun I =>
    if I = [] then f else if h : P I then Classical.choose h else fun _ => 0
  have hF0 : F [] = f := by simp [F]
  have hFI : ∀ I ∈ wordFamily w k, hasWeakWordDeriv X Ω I f (F I) := by
    intro I hI
    by_cases he : I = []
    · subst I
      rw [hF0]
      exact hasWeakWordDeriv_nil X Ω
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hf.1.locallyIntegrable hp))
    · have hi : P I := hf.2 I hI
      simp only [F, ite_eq_right he, dite_eq_left hi]
      exact (Classical.choose_spec hi).1
  apply sobolevXENorm_mul_test_le_with_representatives w X Ω hX k p hp f φ F hF0 hFI
  intro J hJ
  exact Finset.le_sup (f := fun J =>
    eLpNorm (wordDerivative X J φ) ⊤ μ) hJ

end RothschildStein.S
