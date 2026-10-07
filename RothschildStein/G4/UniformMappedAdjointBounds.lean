-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformShortAdjointBounds
public import RothschildStein.G4.MappedAdjointWords

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A numerical constant chosen before the domain and fields
bounds all actual adjoints of a mapped short-field control family through a prescribed order in a persistent short-field frame.
The entire binary bracket is reduced once, preserving the signed weight
and the linear dependence on the determinant persistence factor
(BB Lemma 9.48 and Proposition 9.50, pp. 443–445). -/
theorem exists_uniform_mapped_adjoint_frameCoefficient_bounds
    {ι : Type*} [Fintype ι] (k n s h : ℕ) (w : Fin (k + 1) → ℕ+) (M Δ : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) ((h + 1) * s) M) →
      (∀ y ∈ K, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) y) →
      ∀ I : ι → ShortWord w s, ∀ j : ℕ, j ≤ h → ∀ (J : ShortWord w s) (B : Fin n → ShortWord w s) (i : Fin n)
        (x y : Fin n → ℝ), y ∈ K →
      ∀ (a : ι → ℝ) (e r D : ℝ),
      0 ≤ e → e ≤ 1 → 0 < r → r ≤ 1 → 0 ≤ D →
      (∀ u, |a u| ≤ (e * r) ^ (shortWeight w (I u) : ℕ)) →
      frameDet (shortField w X) B x ≠ 0 →
      (|frameDet (shortField w X) B x| / 2 ≤ |frameDet (shortField w X) B y|) →
      (∀ B' : Fin n → ShortWord w s, |frameDet (shortField w X) B' y| ≤
        D * r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) B') *
          |frameDet (shortField w X) B x|) →
      |frameCoefficient (shortField w X) B
        ((VectorField.lieBracket ℝ (fun z => ∑ u, a u • shortField w X (I u) z))^[j]
          (shortField w X J)) i y| ≤
        (Fintype.card ι : ℝ) ^ j * C * D * e ^ j *
          r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ)) := by
  have hsL : s ≤ (h + 1) * s := by nlinarith
  obtain ⟨C, hC, hbound⟩ := exists_uniform_binary_frameCoefficient_bound
    k n s ((h + 1) * s) w hsL M Δ hM hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hdet I j hj J B i x y hy a e r D he he1 hr hr1 hD ha hBx hhalf hpersist
  have hwords : ∀ L : List ι, L.length = j →
      |frameCoefficient (shortField w X) B
        (orderedAdjoints (fun u => shortField w X (I u)) L (shortField w X J)) i y| ≤
        (C * D) * r ^
          ((((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ)) -
            derivativeWeight (fun u => shortWeight w (I u)) L) := by
    intro L hL
    have hweight : G1.binaryWeight w (orderedShortAdjointWord w J (L.map I)) ≤ (h + 1) * s := by
      have hw := orderedShortAdjointWord_weight_le w J (L.map I)
      rw [List.length_map, hL] at hw
      exact hw.trans (Nat.mul_le_mul_right s (Nat.add_le_add_right hj 1))
    have hb := hbound Ω K hΩ hKΩ X hX hstep hjets hdet
      (orderedShortAdjointWord w J (L.map I)) hweight B i x y hy r D hr hr1 hD hBx hhalf hpersist
    have hmap : derivativeWeight (shortWeight w) (L.map I) =
        derivativeWeight (fun u => shortWeight w (I u)) L := by
      simp only [derivativeWeight, List.map_map, Function.comp_def]
    rw [orderedShortAdjointWord_eval, orderedAdjoints_map,
      orderedShortAdjointWord_weight, hmap] at hb
    have hexp : (((shortWeight w (B i) : ℕ) : ℤ) -
        (((shortWeight w J : ℕ) : ℤ) + derivativeWeight (fun u => shortWeight w (I u)) L)) =
        ((((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ)) -
          derivativeWeight (fun u => shortWeight w (I u)) L) := by ring
    rw [hexp] at hb
    exact hb
  have hb := adjoint_weighted_control_frameCoefficient_bound hΩ
    (fun u => shortField_contDiffOn hΩ hX (I u)) (shortField_contDiffOn hΩ hX J)
    (shortField w X) B (fun u => shortWeight w (I u)) a j i (hKΩ hy) he he1 hr
    (mul_nonneg hC.le hD) ha hwords
  simpa only [mul_assoc] using hb


end RothschildStein.G4
