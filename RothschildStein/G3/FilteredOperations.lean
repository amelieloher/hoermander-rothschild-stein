-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Filtration
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Lower order can be tested on the actual bounded coefficients (BB p. 525). -/
theorem finiteOrderAtLeast_iff {a s : ℕ} {p : Fin a → ℕ+} (k : ℕ)
    (f : FiniteWordAlgebra a s p) :
    FiniteOrderAtLeast k f ↔ ∀ J : BoundedWord a s p,
      wordWeight p J.val < k → f J = 0 := by
  constructor
  · intro h J hJ
    have he := h J.val hJ
    simp only [extend] at he
    split at he
    · exact he
    · rename_i hb
      exact False.elim (hb (boundedWord_weight J))
  · intro h J hJ
    by_cases hb : wordWeight p J ≤ s
    · simp only [extend, dite_eq_left hb]
      exact h (boundedWord p J hb) hJ
    · simp [extend, hb]

/-- Weakening a lower-order bound (BB p. 525). -/
theorem finiteOrderAtLeast_mono {a s : ℕ} {p : Fin a → ℕ+} {k l : ℕ}
    {f : FiniteWordAlgebra a s p} (h : FiniteOrderAtLeast k f) (hl : l ≤ k) :
    FiniteOrderAtLeast l f := fun J hJ => h J (lt_of_lt_of_le hJ hl)

/-- Zero belongs to every filtered layer (BB p. 525). -/
theorem finiteOrderAtLeast_zero_element {a s : ℕ} {p : Fin a → ℕ+} (k : ℕ) :
    FiniteOrderAtLeast k (0 : FiniteWordAlgebra a s p) := by
  rw [finiteOrderAtLeast_iff]
  intro J _
  rfl

/-- Each filtered layer is additive (BB p. 525). -/
theorem finiteOrderAtLeast_add {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f)
    (hg : FiniteOrderAtLeast k g) : FiniteOrderAtLeast k (f + g) := by
  rw [finiteOrderAtLeast_iff] at *
  intro J hJ
  change f J + g J = 0
  rw [hf J hJ, hg J hJ, add_zero]

/-- Each filtered layer is closed under subtraction (BB p. 525). -/
theorem finiteOrderAtLeast_sub {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f)
    (hg : FiniteOrderAtLeast k g) : FiniteOrderAtLeast k (f - g) := by
  rw [finiteOrderAtLeast_iff] at *
  intro J hJ
  change f J - g J = 0
  rw [hf J hJ, hg J hJ, sub_zero]

/-- Each filtered layer is a real vector subspace (BB p. 525). -/
theorem finiteOrderAtLeast_smul {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) (r : ℝ) :
    FiniteOrderAtLeast k (r • f) := by
  rw [finiteOrderAtLeast_iff] at *
  intro J hJ
  change r * f J = 0
  rw [hf J hJ, mul_zero]

/-- Finite sums remain in a fixed filtered layer (BB p. 525). -/
theorem finiteOrderAtLeast_sum {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {ι : Type*} (t : Finset ι) (f : ι → FiniteWordAlgebra a s p)
    (hf : ∀ i ∈ t, FiniteOrderAtLeast k (f i)) : FiniteOrderAtLeast k (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using finiteOrderAtLeast_zero_element k
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact finiteOrderAtLeast_add (hf i (Finset.mem_insert_self i t))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Weighted order zero occurs only at the empty associative word (BB p. 525). -/
theorem weight_eq_zero_iff {a : ℕ} (p : Fin a → ℕ+) (J : List (Fin a)) :
    wordWeight p J = 0 ↔ J = [] := by
  constructor
  · intro h
    have := length_le_weight p J
    have hl : J.length = 0 := by omega
    exact List.length_eq_zero_iff.mp hl
  · rintro rfl
    rfl

/-- Positive-order elements are exactly those with zero constant coefficient
(BB pp. 524–525). -/
theorem finite_positive_order_iff {a s : ℕ} {p : Fin a → ℕ+}
    (f : FiniteWordAlgebra a s p) : FiniteOrderAtLeast 1 f ↔
      f (boundedWord p [] (by simp [wordWeight])) = 0 := by
  rw [finiteOrderAtLeast_iff]
  constructor
  · intro h
    exact h _ (by simp [wordWeight, boundedWord])
  · intro h J hJ
    have hw : wordWeight p J.val = 0 := by omega
    have he := (weight_eq_zero_iff p J.val).mp hw
    have hsub : J = boundedWord p [] (by simp [wordWeight]) := Subtype.ext he
    simpa only [hsub] using h

/-- The fixed Lie span lies in the positive-weight associative ideal
(BB Definitions 10.43–10.45, pp. 524–525). -/
theorem formalSpan_positive_order {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) (hf : f ∈ formalSpan a s p) :
    FiniteOrderAtLeast 1 (f : FiniteWordAlgebra a s p) := by
  apply (finite_positive_order_iff (f : FiniteWordAlgebra a s p)).mpr
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨I, _, _, rfl⟩ := hg
    exact formalBracket_constant_zero I
  | zero => rfl
  | add f g _ _ hf hg => change f _ + g _ = 0; rw [hf, hg, add_zero]
  | smul r f _ hf => change r * f _ = 0; rw [hf, mul_zero]

end RothschildStein.G3
