-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SobolevMultiplication
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n m : ℕ}

/-- Triangle inequality for a finite list of Lᵖ functions (BB p. 73). -/
theorem eLpNorm_list_sum_le {α : Type*} (l : List α) (f : α → (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (μ : Measure (Fin n → ℝ)) :
    eLpNorm (fun x => (l.map (fun a => f a x)).sum) p μ ≤
      (l.map (fun a => eLpNorm (f a) p μ)).sum := by
  have hs := eLpNorm_sum_le (f := fun i : Fin l.length => f (l.get i)) (s := Finset.univ) (μ := μ) hp
  have he : ∀ {β : Type} [AddCommMonoid β] (g : α → β),
      (∑ i : Fin l.length, g (l.get i)) = (l.map g).sum := by
    intro β _ g
    have hm : List.ofFn (fun i : Fin l.length => g (l.get i)) = l.map g := by
      change List.ofFn (g ∘ l.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [← hm, List.sum_ofFn]
  have hf : (∑ i : Fin l.length, f (l.get i)) =
      fun x => (l.map (fun a => f a x)).sum := by
    funext x
    simp only [Finset.sum_apply]
    have hm : List.ofFn (fun i : Fin l.length => f (l.get i) x) =
        l.map (fun a => f a x) := by
      change List.ofFn ((fun a => f a x) ∘ l.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [← hm, List.sum_ofFn]
  rw [hf] at hs
  exact hs.trans_eq (he (fun a => eLpNorm (f a) p μ))

/-- A finite list bounded by C has sum bounded by length times C
(BB p. 73). -/
theorem list_sum_le_length_mul {α : Type*} (l : List α) (F : α → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ a ∈ l, F a ≤ C) : (l.map F).sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hl := ih (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul]
    exact (add_le_add ha hl).trans (by rw [add_comm])

/-- The quantitative cutoff multiplication estimate has constant M bounding every admissible classical cutoff word in L∞; the coefficient is 2^k times the number of weighted words (BB p. 73). -/
theorem sobolevXENorm_mul_test_le_with_representatives (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (F : List (Fin m) → (Fin n → ℝ) → ℝ) (hF0 : F [] = f)
    (hF : ∀ I ∈ wordFamily w k, hasWeakWordDeriv X Ω I f (F I))
    (M : ℝ≥0∞) (hM : ∀ J ∈ wordFamily w k,
      eLpNorm (wordDerivative X J φ) ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) ≤ M) :
    sobolevXENorm w X Ω k p (fun x => f x * φ x) ≤
      (2 ^ k * (wordFamily w k).card : ℕ) * M * sobolevXENorm w X Ω k p f := by
  classical
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  let A := sobolevXENorm w X Ω k p f
  have hword : ∀ I ∈ wordFamily w k,
      weakWordENorm X Ω I p (fun x => f x * φ x) ≤ (2 ^ k : ℕ) * (A * M) := by
    intro I hI
    have hmul := hasWeakWordDeriv_mul_word X Ω hX I f φ φ.contDiff.contDiffOn F hF0
      (fun J hJ => hF J (sublist_mem_wordFamily w k hJ hI))
    rw [weakWordENorm_eq X Ω I p _ _ hmul]
    have ht : ∀ t ∈ leibnizSplits I,
        eLpNorm (fun x => F t.1 x * wordDerivative X t.2 φ x) p μ ≤ A * M := by
      intro t ht
      have hs := leibnizSplits_sublist I t ht
      have h₁ := sublist_mem_wordFamily w k hs.1 hI
      have h₂ := sublist_mem_wordFamily w k hs.2 hI
      have hb : eLpNorm (F t.1) p μ ≤ A := by
        rw [← weakWordENorm_eq X Ω t.1 p f _ (hF t.1 h₁)]
        exact Finset.single_le_sum (fun J _ => (zero_le : 0 ≤ weakWordENorm X Ω J p f)) h₁
      have he : eLpNorm (fun x => F t.1 x * wordDerivative X t.2 φ x) p μ ≤
          eLpNorm (F t.1) p μ * eLpNorm (wordDerivative X t.2 φ) ⊤ μ := by
        simpa using
          (eLpNorm_le_eLpNorm_mul_eLpNorm_top_of_pos (μ := μ)
            (f := F t.1) (g := wordDerivative X t.2 φ) p
            (fun a b : ℝ => a * b) 1
            (continuous_fst.mul continuous_snd)
            (Filter.Eventually.of_forall (fun x => by simp [nnnorm_mul]))
            (lt_of_lt_of_le zero_lt_one hp))
      exact he.trans (mul_le_mul' hb (hM t.2 h₂))
    have htri := eLpNorm_list_sum_le (leibnizSplits I)
      (fun t x => F t.1 x * wordDerivative X t.2 φ x) p hp μ
    have hs := list_sum_le_length_mul (leibnizSplits I)
      (fun t => eLpNorm (fun x => F t.1 x * wordDerivative X t.2 φ x) p μ) (A * M) ht
    have hl := length_le_wordWeight w I
    have hw := (mem_wordFamily_iff w k I).mp hI
    have hpw : (2 ^ I.length : ℕ) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (hl.trans hw)
    change eLpNorm (fun x => ((leibnizSplits I).map _).sum) p μ ≤ _
    exact htri.trans (hs.trans (by rw [leibnizSplits_length]; gcongr))
  unfold sobolevXENorm
  calc
    _ ≤ ∑ I ∈ wordFamily w k, (2 ^ k : ℕ) * (A * M) := Finset.sum_le_sum hword
    _ = _ := by simp [A, sobolevXENorm, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm]

end RothschildStein.S
