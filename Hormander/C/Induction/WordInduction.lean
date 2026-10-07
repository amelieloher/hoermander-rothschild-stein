-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Endpoint

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

/-- Uniformity of constants over the finitely many words of a fixed length. -/
theorem uniform_over_words {m : ℕ} (n : ℕ) (P : List (Fin (m + 1)) → ℝ → Prop)
    (hmono : ∀ I C C', C ≤ C' → P I C → P I C')
    (h : ∀ I : List (Fin (m + 1)), I.length = n → ∃ C : ℝ, 0 < C ∧ P I C) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : List (Fin (m + 1)), I.length = n → P I C := by
  classical
  have h' : ∀ v : List.Vector (Fin (m + 1)) n, ∃ C : ℝ, 0 < C ∧ P v.1 C := fun v =>
    h v.1 v.2
  choose Cv hCv0 hCv using h'
  have hs : 0 ≤ ∑ v, Cv v := Finset.sum_nonneg fun v _ => (hCv0 v).le
  refine ⟨1 + ∑ v, Cv v, by linarith, fun I hI => ?_⟩
  have := hCv ⟨I, hI⟩
  refine hmono _ _ _ ?_ this
  have : Cv ⟨I, hI⟩ ≤ ∑ v, Cv v :=
    Finset.single_le_sum (f := Cv) (fun v _ => (hCv0 v).le) (Finset.mem_univ _)
  linarith

/-- Statement of the horizontal recurrence for the fixed fields. -/
def HorizontalRecurrence {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ Y : RealSchwartzVectorField N,
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin (k + 1)) (u : TestFunction N),
      sobolevNorm (δ - 1) (operatorComm (vectorFieldOperator (X j)) (vectorFieldOperator Y) u) ^ 2 ≤
        C * (normSq (vectorFieldOperator (X j) u) +
          sobolevNorm (2 * δ - 1) (vectorFieldOperator Y u) ^ 2 + normSq u)

/-- The fourfold-loss drift recursion for the fixed fields and coefficient. -/
def DriftRecurrence {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 / 4 → ∀ Y : RealSchwartzVectorField N,
    ∃ C : ℝ, 0 < C ∧ ∀ u : TestFunction N,
      sobolevNorm (α - 1) (operatorComm (vectorFieldOperator (X 0)) (vectorFieldOperator Y) u) ^ 2 ≤
        C * (normSq (diffusionOperator X c u) +
          sobolevNorm (4 * α - 1) (vectorFieldOperator Y u) ^ 2 + normSq u)

/-- The estimate for words of length `n` and parameter `α`. -/
def WordEstimate {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) (n : ℕ) (α : ℝ) (C : ℝ) : Prop :=
  ∀ I : List (Fin (k + 1)), I.length = n → ∀ u : TestFunction N,
    sobolevNorm (α - 1) (vectorFieldOperator (wordField X I) u) ^ 2 ≤
      C * (normSq (diffusionOperator X c u) + normSq u)

theorem WordEstimate.mono {k : ℕ} {X : Fin (k + 1) → RealSchwartzVectorField N}
    {c : SchwartzMap (Carrier N) ℝ} {n : ℕ} {α C C' : ℝ} (h : WordEstimate X c n α C)
    (hC : C ≤ C') : WordEstimate X c n α C' := fun I hI u =>
  (h I hI u).trans (mul_le_mul_of_nonneg_right hC (add_nonneg (normSq_nonneg _) (normSq_nonneg _)))

theorem pow_four_aux (n : ℕ) : (0 : ℝ) < 4 ^ n := by positivity

/-- The word induction follows from the horizontal recurrence, drift recursion, and drift base
estimate. The quantifier order is: fixed data, `ℓ ≥ 1`,
`α ∈ (0, 2/4^ℓ]`, then the constant, then words of length `ℓ` and test functions. -/
theorem word_estimate_induction {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) (hH : HorizontalRecurrence X) (hD : DriftRecurrence X c)
    (hB0 : ∀ α : ℝ, α ≤ 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ u : TestFunction N,
      sobolevNorm (α - 1) (vectorFieldOperator (X 0) u) ^ 2 ≤
        C * (normSq (diffusionOperator X c u) + normSq u)) :
    ∀ n : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α ≤ 2 / 4 ^ n →
      ∃ C : ℝ, 0 < C ∧ WordEstimate X c n α C := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro α hα hα1
    have hα2 : α ≤ 1 / 2 := by norm_num at hα1; linarith
    obtain ⟨C0, hC0, h0⟩ := hB0 α hα2
    obtain ⟨Ch, hCh, hh⟩ := base_horizontal X c hα2
    refine ⟨C0 + Ch, by positivity, fun I hI u => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, I = [j] := by
      match I, hI with
      | [j], _ => exact ⟨j, rfl⟩
    have hpos : 0 ≤ normSq (diffusionOperator X c u) + normSq u :=
      add_nonneg (normSq_nonneg _) (normSq_nonneg _)
    show sobolevNorm (α - 1) (vectorFieldOperator (X j) u) ^ 2 ≤ _
    refine Fin.cases ?_ ?_ j
    · exact (h0 u).trans (mul_le_mul_of_nonneg_right (by linarith) hpos)
    · intro j'
      exact (hh j' u).trans (mul_le_mul_of_nonneg_right (by linarith) hpos)
  | succ n hn ih =>
    intro α hα hα1
    have h4n : (0 : ℝ) < 4 ^ n := pow_four_aux n
    have hα14 : α ≤ 2 / 4 ^ (n + 1) := hα1
    have hαn : 4 * α ≤ 2 / 4 ^ n := by
      have : 2 / (4 : ℝ) ^ (n + 1) = (1 / 2) * (1 / 4 ^ n) := by
        rw [pow_succ]; field_simp; norm_num
      have h2 : α ≤ (1 / 2) * (1 / 4 ^ n) := by rw [← this]; exact hα14
      calc 4 * α ≤ 4 * ((1 / 2) * (1 / 4 ^ n)) := by linarith
        _ = 2 / 4 ^ n := by field_simp; norm_num
    have hαn2 : 2 * α ≤ 2 / 4 ^ n := by
      have : 0 ≤ 2 / (4 : ℝ) ^ n := by positivity
      linarith
    have hα18 : α < 1 / 4 := by
      have h4 : (4 : ℝ) ^ 1 ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
      have : 2 / (4 : ℝ) ^ (n + 1) ≤ 1 / 8 := by
        rw [div_le_iff₀ (by positivity), pow_succ]; nlinarith
      linarith
    obtain ⟨Ca, hCa, hIa⟩ := ih (2 * α) (by linarith) hαn2
    obtain ⟨Cb, hCb, hIb⟩ := ih (4 * α) (by linarith) hαn
    obtain ⟨C6, hC6, hE⟩ := energy_bound X c
    have key : ∀ I : List (Fin (k + 1)), I.length = n + 1 → ∃ C : ℝ, 0 < C ∧
        ∀ u : TestFunction N, sobolevNorm (α - 1) (vectorFieldOperator (wordField X I) u) ^ 2 ≤
          C * (normSq (diffusionOperator X c u) + normSq u) := by
      intro I hI
      match I, hI with
      | j :: I', hI' =>
        have hI'len : I'.length = n := by simpa using hI'
        have hne : I' ≠ [] := by
          intro h; rw [h] at hI'len; simp at hI'len; omega
        rw [vectorField_wordField_cons X j hne]
        refine Fin.cases ?_ ?_ j
        · obtain ⟨C1, hC1, h1⟩ := hD α hα hα18 (wordField X I')
          refine ⟨C1 * (1 + Cb), by positivity, fun u => ?_⟩
          have e := h1 u
          have f := hIb I' hI'len u
          have hp : 0 ≤ normSq (diffusionOperator X c u) + normSq u :=
            add_nonneg (normSq_nonneg _) (normSq_nonneg _)
          refine e.trans ?_
          have : normSq (diffusionOperator X c u) +
              sobolevNorm (4 * α - 1) (vectorFieldOperator (wordField X I') u) ^ 2 + normSq u ≤
              (1 + Cb) * (normSq (diffusionOperator X c u) + normSq u) := by
            have := normSq_nonneg u
            linarith
          nlinarith
        · intro j'
          obtain ⟨C5, hC5, h5⟩ := hH α hα (by linarith) (wordField X I')
          refine ⟨C5 * (C6 + Ca + 1), by positivity, fun u => ?_⟩
          have e := h5 j'.succ u
          have f := hIa I' hI'len u
          have g : normSq (vectorFieldOperator (X j'.succ) u) ≤
              C6 * (normSq (diffusionOperator X c u) + normSq u) :=
            (Finset.single_le_sum (f := fun j : Fin k => normSq (vectorFieldOperator (X j.succ) u))
              (fun i _ => normSq_nonneg _) (Finset.mem_univ j')).trans (hE u)
          have hp : 0 ≤ normSq (diffusionOperator X c u) + normSq u :=
            add_nonneg (normSq_nonneg _) (normSq_nonneg _)
          refine e.trans ?_
          have : normSq (vectorFieldOperator (X j'.succ) u) +
              sobolevNorm (2 * α - 1) (vectorFieldOperator (wordField X I') u) ^ 2 + normSq u ≤
              (C6 + Ca + 1) * (normSq (diffusionOperator X c u) + normSq u) := by
            have := normSq_nonneg (diffusionOperator X c u)
            linarith
          nlinarith
    obtain ⟨C, hC, hall⟩ := uniform_over_words (m := k) (n + 1)
      (fun I C => ∀ u : TestFunction N,
        sobolevNorm (α - 1) (vectorFieldOperator (wordField X I) u) ^ 2 ≤
          C * (normSq (diffusionOperator X c u) + normSq u))
      (fun I C C' hCC h u => (h u).trans (mul_le_mul_of_nonneg_right hCC
        (add_nonneg (normSq_nonneg _) (normSq_nonneg _)))) key
    exact ⟨C, hC, fun I hI u => hall I hI u⟩

/-- And `ε_s ≤ 2/4^ℓ` for `ℓ ≤ s`. -/
theorem gain_le {s ℓ : ℕ} (hs : ℓ ≤ s) : (2 : ℝ) / 4 ^ s ≤ 2 / 4 ^ ℓ := by
  have h1 : (4 : ℝ) ^ ℓ ≤ 4 ^ s := pow_le_pow_right₀ (by norm_num) hs
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1

/-- with the gain `ε_s = 2/4^s`: one constant for all words of
ordinary length `1 ≤ ℓ ≤ s`. -/
theorem word_estimate_gain {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) (hH : HorizontalRecurrence X) (hD : DriftRecurrence X c)
    (hB0 : ∀ α : ℝ, α ≤ 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ u : TestFunction N,
      sobolevNorm (α - 1) (vectorFieldOperator (X 0) u) ^ 2 ≤
        C * (normSq (diffusionOperator X c u) + normSq u)) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ s → WordEstimate X c ℓ (2 / 4 ^ s) C := by
  have hp : (0 : ℝ) < 2 / 4 ^ s := by positivity
  have h : ∀ ℓ : Fin (s + 1), ∃ C : ℝ, 0 < C ∧ (1 ≤ (ℓ : ℕ) → (ℓ : ℕ) ≤ s →
      WordEstimate X c ℓ (2 / 4 ^ s) C) := fun ℓ => by
    by_cases h1 : 1 ≤ (ℓ : ℕ)
    · obtain ⟨C, hC, h⟩ := word_estimate_induction X c hH hD hB0 ℓ h1 (2 / 4 ^ s) hp
        (gain_le (by omega))
      exact ⟨C, hC, fun _ _ => h⟩
    · exact ⟨1, one_pos, fun h _ => absurd h h1⟩
  choose C hC0 hC using h
  have hs : 0 ≤ ∑ ℓ, C ℓ := Finset.sum_nonneg fun ℓ _ => (hC0 ℓ).le
  refine ⟨1 + ∑ ℓ, C ℓ, by linarith, fun ℓ h1 h2 => ?_⟩
  have := hC ⟨ℓ, by omega⟩ h1 h2
  refine WordEstimate.mono this ?_
  have : C ⟨ℓ, by omega⟩ ≤ ∑ ℓ, C ℓ :=
    Finset.single_le_sum (f := C) (fun j _ => (hC0 j).le) (Finset.mem_univ _)
  linarith

end Hormander.C
