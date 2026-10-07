-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.S.WordLeibniz
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n m : ℕ}

/-- Finite sums of Lᵖ representatives stay in Lᵖ (BB p. 73). -/
theorem memLp_list_sum {α : Type*} (l : List α) (f : α → (Fin n → ℝ) → ℝ)
    (p : ℝ≥0∞) (μ : Measure (Fin n → ℝ))
    (h : ∀ a ∈ l, MemLp (f a) p μ) :
    MemLp (fun x => (l.map (fun a => f a x)).sum) p μ := by
  have hs := memLp_finsetSum (Finset.univ : Finset (Fin l.length))
    (fun i _ => h (l.get i) (List.get_mem _ _))
  have he : (fun x => ∑ i : Fin l.length, f (l.get i) x) =
      fun x => (l.map (fun a => f a x)).sum := by
    funext x
    have hm : List.ofFn (fun i : Fin l.length => f (l.get i) x) =
        l.map (fun a => f a x) := by
      change List.ofFn ((fun a => f a x) ∘ l.get) = _
      rw [← List.map_ofFn, List.ofFn_get]
    rw [← hm, List.sum_ofFn]
  rw [he] at hs
  exact hs

/-- Multiplication by a compact smooth test preserves every weighted
Sobolev class (BB p. 73). -/
theorem memSobolevX_mul_test (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ)
    (hf : memSobolevX w X Ω k p f) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    memSobolevX w X Ω k p (fun x => f x * φ x) := by
  classical
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  let P := fun I => ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X Ω I f g ∧ MemLp g p μ
  let F : List (Fin m) → (Fin n → ℝ) → ℝ := fun I =>
    if I = [] then f else if h : P I then Classical.choose h else fun _ => 0
  have hF0 : F [] = f := by simp [F]
  have hFI : ∀ I ∈ wordFamily w k, hasWeakWordDeriv X Ω I f (F I) ∧ MemLp (F I) p μ := by
    intro I hI
    by_cases he : I = []
    · subst I
      rw [hF0]
      exact ⟨hasWeakWordDeriv_nil X Ω
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hf.1.locallyIntegrable hp)), hf.1⟩
    · have hi : P I := hf.2 I hI
      simp only [F, ite_eq_right he, dite_eq_left hi]
      exact Classical.choose_spec hi
  refine ⟨hf.1.fun_mul φ.memLp_top, fun I hI => ?_⟩
  refine ⟨leibnizWordValue X I F φ, ?_, ?_⟩
  · exact hasWeakWordDeriv_mul_word X Ω hX I f φ φ.contDiff.contDiffOn F hF0
      (fun J hJ => (hFI J (sublist_mem_wordFamily w k hJ hI)).1)
  · apply memLp_list_sum
    intro t ht
    have hsub := leibnizSplits_sublist I t ht
    have hfpart := (hFI t.1 (sublist_mem_wordFamily w k hsub.1 hI)).2
    have ha : MemLp (wordDerivative X t.2 φ) ⊤ μ :=
      (wordDerivativeTest Ω X hX t.2 φ).memLp_top
    exact hfpart.fun_mul ha

end RothschildStein.S
