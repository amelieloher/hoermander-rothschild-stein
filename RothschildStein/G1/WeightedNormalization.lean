-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.BracketAlgebra

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C

namespace RothschildStein.G1

/-- Weight of a standard word using the Rothschild–Stein weight (BB p. 10). -/
def nestedWeight {k : ℕ} (w : Fin (k + 1) → ℕ+) (u : NestedWord k) : ℕ :=
  wordWeight w (nestedLetters u)

/-- A generator has its assigned weight (BB Def 1.17, p. 10). -/
theorem nestedWeight_generator {k : ℕ} (w : Fin (k + 1) → ℕ+) (i : Fin (k + 1)) :
    nestedWeight w (.generator i) = (w i : ℕ) := by
  simp [nestedWeight, nestedLetters, wordWeight]

/-- Prepending a letter adds its weight (BB Def 1.17, p. 10). -/
theorem nestedWeight_bracket {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (i : Fin (k + 1)) (u : NestedWord k) :
    nestedWeight w (.bracket i u) = (w i : ℕ) + nestedWeight w u := by
  simp [nestedWeight, nestedLetters, wordWeight]

private theorem raiseOuter_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (i : Fin (k + 1)) (c : WordCombination k) (m : ℕ)
    (hm : ∀ z ∈ c, nestedWeight w z.2 = m) :
    ∀ z ∈ raiseOuter i c, nestedWeight w z.2 = (w i : ℕ) + m := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨p, hp, hpz⟩
  rcases p with ⟨n, u⟩
  cases hpz
  rw [nestedWeight_bracket, hm (n, u) hp]

private theorem negateCombination_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (c : WordCombination k) (m : ℕ) (hm : ∀ z ∈ c, nestedWeight w z.2 = m) :
    ∀ z ∈ negateCombination c, nestedWeight w z.2 = m := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨p, hp, hpz⟩
  rcases p with ⟨n, u⟩
  cases hpz
  exact hm (n, u) hp

/-- Jacobi expansion preserves the sum of weights, including drift weight two
(BB Lemma 1.21 and (1.13), p. 12). -/
theorem bracketExpansion_weight {k : ℕ} (w : Fin (k + 1) → ℕ+) (u v : NestedWord k) :
    ∀ z ∈ bracketExpansion u v, nestedWeight w z.2 = nestedWeight w u + nestedWeight w v := by
  revert v
  induction u with
  | generator i =>
      intro v z hz
      simp only [bracketExpansion, List.mem_singleton] at hz
      cases hz
      simp [nestedWeight_bracket, nestedWeight_generator]
  | bracket i u ih =>
      intro v z hz
      have hz' : z ∈ raiseOuter i (bracketExpansion u v) ∨
          z ∈ negateCombination (bracketExpansion u (.bracket i v)) := by
        simpa [bracketExpansion, List.mem_append] using hz
      rcases hz' with hleft | hright
      · have h := raiseOuter_weight w i (bracketExpansion u v)
          (nestedWeight w u + nestedWeight w v) (ih v) z hleft
        simp only [nestedWeight_bracket] at h ⊢
        omega
      · have h := negateCombination_weight w (bracketExpansion u (.bracket i v))
          (nestedWeight w u + nestedWeight w (.bracket i v)) (ih (.bracket i v)) z hright
        simp only [nestedWeight_bracket] at h ⊢
        omega

private theorem scaleCombination_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (a : ℤ) (c : WordCombination k) (m : ℕ) (hm : ∀ z ∈ c, nestedWeight w z.2 = m) :
    ∀ z ∈ scaleCombination a c, nestedWeight w z.2 = m := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨p, hp, hpz⟩
  rcases p with ⟨n, u⟩
  cases hpz
  exact hm (n, u) hp

private theorem bracketWordExpansion_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (u : NestedWord k) (c : WordCombination k) (n : ℕ)
    (hn : ∀ z ∈ c, nestedWeight w z.2 = n) :
    ∀ z ∈ bracketWordExpansion u c, nestedWeight w z.2 = nestedWeight w u + n := by
  induction c with
  | nil => intro z hz; simp [bracketWordExpansion] at hz
  | cons head c ih =>
      rcases head with ⟨m, v⟩
      intro z hz
      have hz' : z ∈ scaleCombination m (bracketExpansion u v) ∨
          z ∈ bracketWordExpansion u c := by
        simpa [bracketWordExpansion, List.mem_append] using hz
      rcases hz' with hleft | hright
      · have hv := hn (m, v) (by simp)
        have hweight : ∀ y ∈ bracketExpansion u v,
            nestedWeight w y.2 = nestedWeight w u + n := by
          intro y hy
          rw [bracketExpansion_weight w u v y hy, hv]
        exact scaleCombination_weight w m (bracketExpansion u v)
          (nestedWeight w u + n) hweight z hleft
      · exact ih (fun y hy => hn y (by simp [hy])) z hright

private theorem bracketCombination_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (c d : WordCombination k) (m n : ℕ)
    (hm : ∀ z ∈ c, nestedWeight w z.2 = m) (hn : ∀ z ∈ d, nestedWeight w z.2 = n) :
    ∀ z ∈ bracketCombination c d, nestedWeight w z.2 = m + n := by
  induction c with
  | nil => intro z hz; simp [bracketCombination] at hz
  | cons head c ih =>
      rcases head with ⟨a, u⟩
      intro z hz
      have hz' : z ∈ scaleCombination a (bracketWordExpansion u d) ∨
          z ∈ bracketCombination c d := by
        simpa [bracketCombination, List.mem_append] using hz
      rcases hz' with hleft | hright
      · have hu := hm (a, u) (by simp)
        have hword : ∀ y ∈ bracketWordExpansion u d, nestedWeight w y.2 = m + n := by
          intro y hy
          rw [bracketWordExpansion_weight w u d n hn y hy, hu]
        exact scaleCombination_weight w a (bracketWordExpansion u d) (m + n) hword z hleft
      · exact ih (fun y hy => hm y (by simp [hy])) z hright

/-- Each term in the field-independent binary normalization has exactly the
weight of the binary expression (BB Lemma 1.21, p. 12). -/
theorem binaryExpansion_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (t : Hormander.Interface.LieWord k) :
    ∀ z ∈ binaryExpansion t, nestedWeight w z.2 = binaryWeight w t := by
  induction t with
  | generator i =>
      intro z hz
      simp only [binaryExpansion, List.mem_singleton] at hz
      cases hz
      exact nestedWeight_generator w i
  | bracket p q ihp ihq =>
      exact bracketCombination_weight w (binaryExpansion p) (binaryExpansion q)
        (binaryWeight w p) (binaryWeight w q) ihp ihq

end RothschildStein.G1
