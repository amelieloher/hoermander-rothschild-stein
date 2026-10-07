-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.UniformWordApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- A continuous function and its continuous weak first field derivative have simultaneous smooth compactly supported approximants converging uniformly on each interior patch (BB Theorem 2.20, p. 86). -/
theorem exists_firstField_uniform_approximation
    (Ω U : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (hc : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hUΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => X) Ω [0] f g) :
    ∃ F : ℝ → (Fin n → ℝ) → ℝ,
      (∀ ε : ℝ,0 < ε → ContDiff ℝ (⊤ : ℕ∞) (F ε) ∧ HasCompactSupport (F ε)) ∧
      TendstoUniformlyOn F f (𝓝[>] 0) (U : Set (Fin n → ℝ)) ∧
      TendstoUniformlyOn (fun ε => fieldDerivative X (F ε)) g (𝓝[>] 0)
        (U : Set (Fin n → ℝ)) := by
  let w : Fin 1 → ℕ+ := fun _ => 1
  let jet := fun I : List (Fin 1) => if I = [] then f else g
  have hs : ∀ I ∈ wordFamily w 1,I = [] ∨ I = [0] := by
    intro I hI
    have hl := (length_le_wordWeight w I).trans ((mem_wordFamily_iff w 1 I).mp hI)
    cases I with
    | nil => exact Or.inl rfl
    | cons i I =>
      have ht : I.length = 0 := by simp only [List.length_cons] at hl; omega
      have hi : i = 0 := Subsingleton.elim _ _
      exact Or.inr (by rw [List.length_eq_zero_iff.mp ht,hi])
  have hn : jet [] = f := by simp [jet]
  have hw' : ∀ I ∈ wordFamily w 1,hasWeakWordDeriv (fun _ : Fin 1 => X) Ω I f (jet I) := by
    intro I hI
    rcases hs I hI with rfl | rfl
    · simpa only [jet,ite_eq_left rfl] using hasWeakWordDeriv_nil (fun _ : Fin 1 => X) Ω hw.1
    · simpa only [jet,List.cons_ne_nil,ite_false] using hw
  have hc' : ∀ I ∈ wordFamily w 1,ContinuousOn (jet I) (Ω : Set (Fin n → ℝ)) := by
    intro I hI
    rcases hs I hI with rfl | rfl
    · simpa only [jet,ite_eq_left rfl] using hf
    · simpa only [jet,List.cons_ne_nil,ite_false] using hg
  obtain ⟨χ,δ,hd,hχ,hsm,ht⟩ := exists_cutoff_uniform_word_approximation w
    (fun _ : Fin 1 => X) Ω U (fun _ => hX) hc hUΩ 1 f jet hn hw' hc'
  refine ⟨fun ε => euclideanRegularize n (fun x => f x*χ x) ε,hsm,?_,?_⟩
  · simpa only [wordDerivative,hn] using ht [] (nil_mem_wordFamily w 1)
  · have hi : [0] ∈ wordFamily w 1 := by simp [mem_wordFamily_iff,wordWeight,w]
    simpa only [wordDerivative,jet,List.cons_ne_nil,ite_false] using ht [0] hi

end RothschildStein.S
