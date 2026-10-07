-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.OriginalCoefficientRemainderJets
public import RothschildStein.G4.ZeroCoefficientRemainderJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual differentiated coefficient remainder estimate holds
for all small coefficients, including the coefficient origin, through the
retained Taylor order (BB Lemma 9.48, pp. 441–443). -/
theorem norm_original_coefficient_remainder_jet_le_including_zero {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set (Fin N → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) (hz : z ∈ A) (hznorm : ‖z‖ ≤ 1) (i : Fin m) {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w))
        (∑ j, p.1 j • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U)
    (hforward : ∀ s ∈ Icc (0 : ℝ) 1, Φ ((z, x), s) ∈ U)
    {B : ℝ} (hB : 0 ≤ B)
    (hjet : ∀ y ∈ Ω, ∀ j, ∀ l ≤ R + 1, ‖iteratedFDeriv ℝ l (W j) y‖ ≤ B)
    (hsmall : RothschildStein.G1.spatialJetRate (R + 1)
      ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B * ‖z‖) < 1)
    (q n : ℕ) (hnq : n + (q + 1) ≤ R) (hnqpow : n ≤ q) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
      fun p => ∑ j, p.1 j • W j p.2
    let Y : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => W i p.2
    let C := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ (q + 1) *
      ((R + 1).factorial * B)
    ‖iteratedFDeriv ℝ n (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
      fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) (p.1, Φ ((p.1, p.2), 1)))) (z, x)‖ ≤
      (n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n) * ‖z‖ ^ (q + 1 - n) := by
  intro Z Y C
  rcases eq_or_lt_of_le (norm_nonneg z) with hzero | hpos
  · have hz0 : z = 0 := norm_eq_zero.mp hzero.symm
    subst z
    have he := linear_field_flow_coefficient_remainder_zero_jets hA hΩ hU hUΩ W hW
      hz i hτ Φ hc hΦ hx hB hjet q (by omega) n hnqpow
    rw [he, norm_zero]
    have hC : 0 ≤ C := by dsimp [C]; positivity
    positivity
  · exact norm_original_coefficient_remainder_jet_le hA hΩ hU hUΩ W hW z hz hpos hznorm
      i hτ Φ hc hΦ hx hforward hB hjet hsmall q n hnq (by omega)

end RothschildStein.G4
