-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A finite ambient coefficient-jet budget, computed within the
original open smoothness domain (BB Convention 1.26, pp. 13–14). -/
def HasJetBound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω K : Set E) (f : E → F) (h : ℕ) (M : ℝ) : Prop :=
  ∀ j, j ≤ h → ∀ x ∈ K, ‖iteratedFDerivWithin ℝ j f Ω x‖ ≤ M

/-- Ambient derivative jets on an open domain are exactly the
next jets of the original function (BB coefficient-jet convention). -/
theorem norm_iteratedFDerivWithin_fderiv_of_isOpen {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} (hΩ : IsOpen Ω) (f : E → F) {x : E} (hx : x ∈ Ω) (j : ℕ) :
    ‖iteratedFDerivWithin ℝ j (fderiv ℝ f) Ω x‖ =
      ‖iteratedFDerivWithin ℝ (j + 1) f Ω x‖ := by
  rw [iteratedFDerivWithin_congr (fun y hy => (fderivWithin_of_isOpen hΩ hy).symm) hx j,
    norm_iteratedFDerivWithin_fderivWithin hΩ.uniqueDiffOn hx]

/-- Differentiation shifts a finite jet budget by one. -/
theorem HasJetBound.fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → F} {h : ℕ} {M : ℝ} (hf : HasJetBound Ω K f (h + 1) M) :
    HasJetBound Ω K (fderiv ℝ f) h M := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderiv_of_isOpen hΩ f (hKΩ hx) j]
  exact hf _ (Nat.add_le_add_right hj 1) x hx

/-- A bilinear operation preserves finite coefficient-jet budgets
with an explicit universal order-dependent factor
(BB Lemma 9.31, pp. 422–423; Mathlib quantitative Leibniz formula). -/
theorem HasJetBound.bilinear {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    {h : ℕ} {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hfP : HasJetBound Ω K f h P) (hgQ : HasJetBound Ω K g h Q) :
    HasJetBound Ω K (fun x => B (f x) (g x)) h (‖B‖ * 2 ^ h * P * Q) := by
  intro j hj x hx
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear hf hg hΩ.uniqueDiffOn (hKΩ hx)
    (n := j) (by simp)
  have hs : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ i f Ω x‖ * ‖iteratedFDerivWithin ℝ (j - i) g Ω x‖) ≤
      2 ^ j * P * Q := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * P * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ h := (Finset.mem_range_succ_iff.mp hi).trans hj
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hfP i hi' x hx) (by positivity))
          (hgQ (j - i) ((Nat.sub_le j i).trans hj) x hx) (norm_nonneg _) (mul_nonneg (by positivity) hP)
      _ = (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) * P * Q := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ = _ := by
        have hh : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hh]
  calc
    _ ≤ ‖B‖ * (2 ^ j * P * Q) := hb.trans (mul_le_mul_of_nonneg_left hs B.opNorm_nonneg)
    _ ≤ ‖B‖ * (2 ^ h * P * Q) := by
      apply mul_le_mul_of_nonneg_left _ B.opNorm_nonneg
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hP) hQ
    _ = _ := by ring

end RothschildStein.G4
