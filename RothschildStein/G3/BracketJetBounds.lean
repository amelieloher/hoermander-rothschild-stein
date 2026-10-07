-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FieldPowerBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Leibniz's binomial bound for a vector-valued field derivative
(BB Lemma 9.22, pp. 413–414). -/
theorem norm_iteratedFDeriv_vectorDerivative_le {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (n : ℕ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ V y (U y)) x‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ‖iteratedFDeriv ℝ (j + 1) V x‖ * ‖iteratedFDeriv ℝ (n - j) U x‖ := by
  have hh := norm_iteratedFDerivWithin_clm_apply (n := n)
    (hV.fderiv_of_isOpen Ω.isOpen (by simp)) hU Ω.isOpen.uniqueDiffOn hx (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx, norm_iteratedFDeriv_fderiv] at hh
  exact hh

/-- Finite vector-field jet bounds give an explicit binomial constant
for their derivative pairing (BB Lemma 9.22, pp. 413–414). -/
theorem norm_vectorDerivative_jet_le {N R n : ℕ}
    (Ω : Opens (Fin N → ℝ)) (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hn : n + 1 ≤ R) {B F : ℝ}
    (hUjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j U x‖ ≤ B)
    (hVjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j V x‖ ≤ F) :
    ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ V y (U y)) x‖ ≤ 2 ^ n * F * B := by
  apply (norm_iteratedFDeriv_vectorDerivative_le Ω U V hU hV n hx).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * F * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hF : 0 ≤ F := (norm_nonneg _).trans (hVjet 0 (Nat.zero_le R))
      gcongr
      · exact hVjet (j + 1) (by omega)
      · exact hUjet (n - j) (by omega)
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      rfl
end RothschildStein.G3
