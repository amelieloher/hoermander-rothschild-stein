-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BudgetedCoefficientDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Differentiating an actual generator product increases its
factor allowance by one and has an explicit coefficient budget linear in
the number of original factors. -/
theorem generatorValue_derivative_budget {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω)
    {w : Fin (k + 1) → ℕ+} {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L : ShortWord w s) (M : List (Fin n × ShortWord w s)) {h : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hjets : ∀ L J K : ShortWord w s,
      HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) h A) :
    HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B (M.length + 1)
      (generatorDeficit (shortWeight w) B M - ((shortWeight w L : ℕ) : ℤ)) h
      (fieldDerivative (shortField w X L) (generatorValue (shortField w X) B M))
      ((M.length : ℝ) * ((Fintype.card (ShortWord w s) : ℝ) * ((n : ℝ) + 1) * A)) := by
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  let D := (Fintype.card (ShortWord w s) : ℝ) * ((n : ℝ) + 1) * A
  induction M with
  | nil =>
    simpa only [List.length_nil, Nat.cast_zero, zero_mul] using
      (HasBudgetedGeneratorExpansion.zero.congr (g := fieldDerivative (Z L) (generatorValue Z B []))
        (fun x _ => by
          change (fderiv ℝ (fun _ : Fin n → ℝ => (1 : ℝ)) x) (Z L x) = 0
          simp))
  | cons z M ih =>
    have hgM : IsGenerator Z v B M.length (generatorDeficit v B M) (generatorValue Z B M) :=
      ⟨M, le_rfl, le_rfl, rfl⟩
    have hfirst := budgetedExpansion_mul_generator
      (short_frameCoefficient_derivative_budget hΩ hKΩ hX hstep B L z.2 z.1 hA hjets) hgM
    have hsecond := budgetedExpansion_mul_generator ih (frameCoefficient_isGenerator Z v B z.1 z.2)
    have hfirst' : HasBudgetedGeneratorExpansion Ω K₀ Z v B ((z :: M).length + 1)
        (generatorDeficit v B (z :: M) - ((v L : ℕ) : ℤ)) h
        (fun x => fieldDerivative (Z L) (frameCoefficient Z B (Z z.2) z.1) x * generatorValue Z B M x) D := by
      convert hfirst using 1 <;> simp only [v, List.length_cons, generatorDeficit, List.map_cons, List.sum_cons] <;> omega
    have hsecond' : HasBudgetedGeneratorExpansion Ω K₀ Z v B ((z :: M).length + 1)
        (generatorDeficit v B (z :: M) - ((v L : ℕ) : ℤ)) h
        (fun x => frameCoefficient Z B (Z z.2) z.1 x * fieldDerivative (Z L) (generatorValue Z B M) x)
        ((M.length : ℝ) * D) := by
      have hb := hsecond.congr
        (g := fun x => frameCoefficient Z B (Z z.2) z.1 x * fieldDerivative (Z L) (generatorValue Z B M) x)
        (fun x _ => mul_comm _ _)
      convert hb using 1
      simp only [v, generatorDeficit, List.map_cons, List.sum_cons]
      omega
    have hb := (HasBudgetedGeneratorExpansion.add hfirst' hsecond').congr
      (g := fieldDerivative (Z L) (generatorValue Z B (z :: M))) (fun x hx => by
        rw [fieldDerivative_generatorValue hΩ (shortField_contDiffOn hΩ hX) B (Z L) (z :: M) hx.1 hx.2]
        change generatorDerivativeValue Z B (Z L) (z :: M) x = _
        rw [generatorDerivativeValue, ← fieldDerivative_generatorValue hΩ
          (shortField_contDiffOn hΩ hX) B (Z L) M hx.1 hx.2])
    convert hb using 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- Arbitrary generators inherit the same derivative budget,
using their factor allowance rather than their chosen product length. -/
theorem generator_derivative_budget {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω)
    {w : Fin (k + 1) → ℕ+} {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L : ShortWord w s) {a h : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hjets : ∀ L J K : ShortWord w s,
      HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) h A)
    (hf : IsGenerator (shortField w X) (shortWeight w) B a p f) :
    HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B (a + 1)
      (p - ((shortWeight w L : ℕ) : ℤ)) h (fieldDerivative (shortField w X L) f)
      ((a : ℝ) * ((Fintype.card (ShortWord w s) : ℝ) * ((n : ℝ) + 1) * A)) := by
  obtain ⟨M, hM, hp, rfl⟩ := hf
  have hb := generatorValue_derivative_budget hΩ hKΩ hX hstep B L M hA hjets
  have hb' := budgetedExpansion_mono (Nat.add_le_add_right hM 1)
    (sub_le_sub_right hp _) le_rfl hb
  apply hb'.enlarge
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM) (by positivity)

end RothschildStein.G4
