-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FiniteCoverLpNorm
public import RothschildStein.S.Sobolev
public import RothschildStein.H3.WeakJetNormFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The Sobolev norm `sobolevXENorm` is bounded by the sum over
an overlapping finite open cover, using the same actual weak jets. -/
theorem sobolevXENorm_le_finite_open_cover {n m : ℕ} {ι : Type*}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (s : Finset ι) (A : ι → Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (hA : ∀ i ∈ s, (A i : Set (Fin n → ℝ)) ⊆ Ω)
    (hcover : ∀ x ∈ U, ∃ i ∈ s, x ∈ A i)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX w X Ω k p u) :
    sobolevXENorm w X U k p u ≤ ∑ i ∈ s, sobolevXENorm w X (A i) k p u := by
  classical
  have hb : ∀ I ∈ wordFamily w k,
      weakWordENorm X U I p u ≤ ∑ i ∈ s, weakWordENorm X (A i) I p u := by
    intro I hI
    obtain ⟨g,hg,hgp⟩ := hu.2 I hI
    rw [S.weakWordENorm_eq X U I p u g (S.hasWeakWordDeriv_restrict X Ω U hU hg)]
    have hnorm : ∀ i ∈ s, weakWordENorm X (A i) I p u =
        eLpNorm g p (volume.restrict (A i : Set (Fin n → ℝ))) := by
      intro i hi
      exact S.weakWordENorm_eq X (A i) I p u g
        (S.hasWeakWordDeriv_restrict X Ω (A i) (hA i hi) hg)
    rw [Finset.sum_congr rfl hnorm]
    exact eLpNorm_le_finite_open_cover Ω U s A hU hA hcover p hp g hgp
  unfold sobolevXENorm
  exact (Finset.sum_le_sum hb).trans_eq (Finset.sum_comm)

/-- Actual Sobolev membership makes every term of the fixed finite norm finite. -/
theorem sobolevXENorm_lt_top_of_memSobolev {n m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX w X Ω k p u) : sobolevXENorm w X Ω k p u < ⊤ := by
  unfold sobolevXENorm
  exact ENNReal.sum_lt_top.mpr (fun I hI => weakWordENorm_lt_top_of_memSobolev w X Ω k p u hu I hI)

/-- The finite-cover bound in real norms, with finiteness proved from membership. -/
theorem sobolevXENorm_toReal_le_finite_open_cover {n m : ℕ} {ι : Type*}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (s : Finset ι) (A : ι → Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (hA : ∀ i ∈ s, (A i : Set (Fin n → ℝ)) ⊆ Ω)
    (hcover : ∀ x ∈ U, ∃ i ∈ s, x ∈ A i)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX w X Ω k p u) :
    (sobolevXENorm w X U k p u).toReal ≤
      ∑ i ∈ s, (sobolevXENorm w X (A i) k p u).toReal := by
  have hfinite : ∀ i ∈ s, sobolevXENorm w X (A i) k p u ≠ ⊤ := by
    intro i hi
    exact (sobolevXENorm_lt_top_of_memSobolev w X (A i) k p u
      (S.memSobolevX_restrict w X Ω (A i) (hA i hi) hu)).ne
  have hb := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfinite)
    (sobolevXENorm_le_finite_open_cover w X Ω U s A hU hA hcover k p hp u hu)
  rw [ENNReal.toReal_sum hfinite] at hb
  exact hb

end RothschildStein.H3
