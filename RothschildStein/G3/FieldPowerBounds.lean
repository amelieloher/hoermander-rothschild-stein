-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialPowerJets
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- One field derivative costs one function jet and only finitely
many field jets, with an explicit binomial bound (BB pp. 410–415). -/
theorem norm_iteratedFDeriv_fieldDerivative_le {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (n : ℕ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ n (fieldDerivative V f) x‖ ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ‖iteratedFDeriv ℝ (j + 1) f x‖ * ‖iteratedFDeriv ℝ (n - j) V x‖ := by
  have hh := norm_iteratedFDerivWithin_clm_apply (n := n)
    (hf.fderiv_of_isOpen Ω.isOpen (by simp)) hV Ω.isOpen.uniqueDiffOn hx (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen hx, norm_iteratedFDeriv_fderiv] at hh
  exact hh

/-- A uniform finite field jet bound gives an explicit one-step
bound for the differentiated function (BB pp. 410–415). -/
theorem norm_fieldDerivative_jet_le {N R n : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hn : n + 1 ≤ R) {B F : ℝ}
    (hVjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j V x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f x‖ ≤ F) :
    ‖iteratedFDeriv ℝ n (fieldDerivative V f) x‖ ≤ 2 ^ n * F * B := by
  apply (norm_iteratedFDeriv_fieldDerivative_le Ω V hV f hf n hx).trans
  calc
    (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      ‖iteratedFDeriv ℝ (j + 1) f x‖ * ‖iteratedFDeriv ℝ (n - j) V x‖) ≤
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * F * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hF : 0 ≤ F := (norm_nonneg _).trans (hfjet 0 (Nat.zero_le R))
      gcongr
      · exact hfjet (j + 1) (by omega)
      · exact hVjet (n - j) (by omega)
    _ = 2 ^ n * F * B := by
      simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      rfl
/-- A length-m field power costs exactly m function jets and has a
bound polynomial in the finite coefficient norm (BB pp. 410–415). -/
theorem norm_fieldPower_jet_le {N R : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B F : ℝ}
    (hVjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j V x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (m n : ℕ) (hmn : n + m ≤ R) :
    ‖iteratedFDeriv ℝ n (fieldPower V m f) x‖ ≤ (2 ^ R * B) ^ m * F := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hVjet 0 (Nat.zero_le R))
  have hF : 0 ≤ F := (norm_nonneg _).trans (hfjet 0 (Nat.zero_le R))
  induction m generalizing n with
  | zero => simpa only [fieldPower, pow_zero, one_mul] using hfjet n (by omega)
  | succ m ih =>
    rw [fieldPower_succ]
    have hfj : ∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j (fieldPower V m f) x‖ ≤
        (2 ^ R * B) ^ m * F := fun j hj => ih j (by omega)
    have hb := norm_fieldDerivative_jet_le (R := n + 1) Ω V hV (fieldPower V m f)
      (contDiffOn_fieldPower Ω V hV m f hf) hx le_rfl
      (fun j hj => hVjet j (by omega)) hfj
    apply hb.trans
    calc
      2 ^ n * ((2 ^ R * B) ^ m * F) * B ≤
          2 ^ R * ((2 ^ R * B) ^ m * F) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hB) _) hF)
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n ≤ R)
      _ = (2 ^ R * B) ^ (m + 1) * F := by rw [pow_succ]; ring

end RothschildStein.G3
