-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformMappedAdjointBounds
public import RothschildStein.G4.AdjointTaylorCorrections

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The positive Taylor terms of the actual mapped control field
are bounded by one numerical polynomial, chosen before the primitive
fields and frame. The persistence factor occurs linearly (BB pp. 443–445). -/
theorem exists_uniform_mapped_taylor_correction_bound (k n s m q : ℕ)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) ((q + 1) * s) M) →
      (∀ y ∈ K, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) y) →
      ∀ I : Fin m → ShortWord w s, ∀ (J : ShortWord w s) (B : Fin n → ShortWord w s)
        (i : Fin n) (x y : Fin n → ℝ), y ∈ K →
      ∀ (a : Fin m → ℝ) (e r D : ℝ),
      0 ≤ e → e ≤ 1 → 0 < r → r ≤ 1 → 0 ≤ D →
      (∀ u, |a u| ≤ (e * r) ^ (shortWeight w (I u) : ℕ)) →
      frameDet (shortField w X) B x ≠ 0 →
      (|frameDet (shortField w X) B x| / 2 ≤ |frameDet (shortField w X) B y|) →
      (∀ B' : Fin n → ShortWord w s, |frameDet (shortField w X) B' y| ≤
        D * r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) B') *
          |frameDet (shortField w X) B x|) →
      let V := fun z => ∑ u, a u • shortField w X (I u) z
      |frameCoefficient (shortField w X) B (fun z =>
        ∑ j : Fin q, ((-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)) •
          ((VectorField.lieBracket ℝ V)^[j.val + 1] (shortField w X J)) z) i y| ≤
        (∑ j : Fin q, |(-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)| *
          (m : ℝ) ^ (j.val + 1) * C * D * e ^ (j.val + 1)) *
            r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_mapped_adjoint_frameCoefficient_bounds
    (ι := Fin m) k n s q w M Δ hM hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hdet I J B i x y hy a e r D he he1 hr hr1 hD ha hBx hhalf hpersist V
  have hb := adjoint_taylor_correction_frameCoefficient_le (shortField w X) B V
    (shortField w X J) q
    (fun j => (-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)) i y
    (fun j => (m : ℝ) ^ (j.val + 1) * C * D)
    (fun j => by
      simpa only [Fintype.card_fin] using hbound Ω K hΩ hKΩ X hX hstep hjets hdet
        I (j.val + 1) (by omega) J B i x y hy a e r D he he1 hr hr1 hD ha hBx hhalf hpersist)
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

end RothschildStein.G4
