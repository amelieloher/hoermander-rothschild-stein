-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortGeneratorDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Differentiating a product of actual frame coefficients adds
at most one factor and subtracts the differentiating field's weight
(BB Proposition 9.36, pp. 427–428). -/
theorem generatorValue_derivative_expansion {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L : ShortWord w s) (M : List (Fin n × ShortWord w s)) :
    HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B (M.length + 1)
      (generatorDeficit (shortWeight w) B M - ((shortWeight w L : ℕ) : ℤ))
      (fieldDerivative (shortField w X L) (generatorValue (shortField w X) B M)) := by
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  induction M with
  | nil =>
    exact HasGeneratorExpansion.zero.congr (fun x _ => by
      change (fderiv ℝ (fun _ : Fin n → ℝ => (1 : ℝ)) x) (Z L x) = 0
      simp)
  | cons z M ih =>
    have hgM : IsGenerator Z v B M.length (generatorDeficit v B M) (generatorValue Z B M) :=
      ⟨M, le_rfl, le_rfl, rfl⟩
    have hfirst := generatorExpansion_mul
      (short_frameCoefficient_derivative_expansion hΩ hX hstep B L z.2 z.1)
      (generator_expansion (Ω := Ω) hgM)
    have hsecond := generatorExpansion_mul
      (generator_expansion (Ω := Ω) (frameCoefficient_isGenerator Z v B z.1 z.2)) ih
    have hfirst' : HasGeneratorExpansion Ω Z v B ((z :: M).length + 1)
        (generatorDeficit v B (z :: M) - ((v L : ℕ) : ℤ))
        (fun x => fieldDerivative (Z L) (frameCoefficient Z B (Z z.2) z.1) x * generatorValue Z B M x) := by
      convert hfirst using 1 <;> simp only [v, List.length_cons, generatorDeficit, List.map_cons, List.sum_cons] <;> omega
    have hsecond' : HasGeneratorExpansion Ω Z v B ((z :: M).length + 1)
        (generatorDeficit v B (z :: M) - ((v L : ℕ) : ℤ))
        (fun x => frameCoefficient Z B (Z z.2) z.1 x * fieldDerivative (Z L) (generatorValue Z B M) x) := by
      convert hsecond using 1 <;> simp only [v, List.length_cons, generatorDeficit, List.map_cons, List.sum_cons] <;> omega
    exact (HasGeneratorExpansion.add hfirst' hsecond').congr (fun x hx => by
      rw [fieldDerivative_generatorValue hΩ (shortField_contDiffOn hΩ hX) B (Z L) (z :: M) hx.1 hx.2]
      change generatorDerivativeValue Z B (Z L) (z :: M) x = _
      rw [generatorDerivativeValue, ← fieldDerivative_generatorValue hΩ
        (shortField_contDiffOn hΩ hX) B (Z L) M hx.1 hx.2])

/-- Differentiation of an arbitrary generator has the precise
factor-count and signed-deficit change, with no loss to natural subtraction
(BB Proposition 9.36, pp. 427–428). -/
theorem generator_derivative_expansion {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L : ShortWord w s) {a : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsGenerator (shortField w X) (shortWeight w) B a p f) :
    HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B (a + 1)
      (p - ((shortWeight w L : ℕ) : ℤ)) (fieldDerivative (shortField w X L) f) := by
  obtain ⟨M, hM, hp, rfl⟩ := hf
  exact generatorExpansion_mono (Nat.add_le_add_right hM 1) (sub_le_sub_right hp _)
    (generatorValue_derivative_expansion hΩ hX hstep B L M)

end RothschildStein.G4
