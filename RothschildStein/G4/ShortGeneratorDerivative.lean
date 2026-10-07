-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortBracketReduction
public import RothschildStein.G4.GeneratorProducts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A differentiated single coefficient has at most two factors
and loses exactly the differentiating field's weight in its deficit
(BB Proposition 9.36, pp. 427–428). -/
theorem short_frameCoefficient_derivative_expansion {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L J : ShortWord w s) (i : Fin n) :
    HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B 2
      (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ) -
        ((shortWeight w L : ℕ) : ℤ))
      (fieldDerivative (shortField w X L)
        (frameCoefficient (shortField w X) B (shortField w X J) i)) := by
  classical
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  let p : ℤ := ((v (B i) : ℕ) : ℤ) - ((v J : ℕ) : ℤ) - ((v L : ℕ) : ℤ)
  have hfirst : ∀ K : ShortWord w s,
      HasGeneratorExpansion Ω Z v B 2 p
        (fun x => shortBracketCoefficient w X L J K x * frameCoefficient Z B (Z K) i x) := by
    intro K
    by_cases hweight : (v L : ℕ) + (v J : ℕ) < (v K : ℕ)
    · have hc := shortBracketCoefficient_eq_zero_of_weight_lt w X L J K hweight
      exact HasGeneratorExpansion.zero.congr (fun x _ => by simp only [congrFun hc x, Pi.zero_apply, zero_mul])
    · have hw : (v K : ℕ) ≤ (v L : ℕ) + (v J : ℕ) := le_of_not_gt hweight
      have hw' : ((v K : ℕ) : ℤ) ≤ ((v L : ℕ) : ℤ) + ((v J : ℕ) : ℤ) := by exact_mod_cast hw
      have hg := generator_mono (show 1 ≤ 2 by omega)
        (show p ≤ ((v (B i) : ℕ) : ℤ) - ((v K : ℕ) : ℤ) by dsimp [p]; omega)
        (frameCoefficient_isGenerator Z v B i K)
      exact HasGeneratorExpansion.term _ _ (shortBracketCoefficient_contDiffOn hΩ hX hstep L J K) hg
  have hsecond : ∀ j : Fin n, ∀ K : ShortWord w s,
      HasGeneratorExpansion Ω Z v B 2 p
        (fun x => shortBracketCoefficient w X L (B j) K x *
          (frameCoefficient Z B (Z J) j x * frameCoefficient Z B (Z K) i x)) := by
    intro j K
    by_cases hweight : (v L : ℕ) + (v (B j) : ℕ) < (v K : ℕ)
    · have hc := shortBracketCoefficient_eq_zero_of_weight_lt w X L (B j) K hweight
      exact HasGeneratorExpansion.zero.congr (fun x _ => by simp only [congrFun hc x, Pi.zero_apply, zero_mul])
    · have hw : (v K : ℕ) ≤ (v L : ℕ) + (v (B j) : ℕ) := le_of_not_gt hweight
      have hw' : ((v K : ℕ) : ℤ) ≤ ((v L : ℕ) : ℤ) + ((v (B j) : ℕ) : ℤ) := by exact_mod_cast hw
      have hg := generator_mul (frameCoefficient_isGenerator Z v B j J)
        (frameCoefficient_isGenerator Z v B i K)
      have hg' := generator_mono (show 1 + 1 ≤ 2 by omega)
        (show p ≤ (((v (B j) : ℕ) : ℤ) - ((v J : ℕ) : ℤ)) +
          (((v (B i) : ℕ) : ℤ) - ((v K : ℕ) : ℤ)) by dsimp [p]; omega) hg
      exact HasGeneratorExpansion.term _ _ (shortBracketCoefficient_contDiffOn hΩ hX hstep L (B j) K) hg'
  have hf := generatorExpansion_sum Finset.univ _ (fun K _ => hfirst K)
  have hs := generatorExpansion_sum Finset.univ _ (fun j _ =>
    generatorExpansion_sum Finset.univ _ (fun K _ => hsecond j K))
  exact (generatorExpansion_sub hf hs).congr (fun x hx =>
    short_fieldDerivative_frameCoefficient hΩ hX hstep B L J i hx.1 hx.2)

end RothschildStein.G4
