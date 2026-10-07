-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.OriginalCoefficientScaledAdjointJets
public import RothschildStein.G4.CoefficientRemainderSmoothness
public import RothschildStein.G4.UnscaledCoefficientJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- ACTUAL unscaled joint coefficient/initial-point jets of the
original coefficient derivative remainder have the differentiated remainder
power ‖z‖^(q+1-n), using exact derivative reparametrization and primitive
finite field jets (BB Lemma 9.48, pp. 441–443). -/
theorem norm_original_coefficient_remainder_jet_le {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set (Fin N → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) (hz : z ∈ A) (hzpos : 0 < ‖z‖) (hznorm : ‖z‖ ≤ 1) (i : Fin m) {τ : ℝ} (hτ : 1 < τ)
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
    (q n : ℕ) (hnq : n + (q + 1) ≤ R) (hnqpow : n ≤ q + 1) :
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
  let F : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p =>
    fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1) -
      ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        (((spatialBracketFamily Z)^[j] Y) (p.1, Φ (p, 1)))
  let M : ℝ := n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ U) :=
    linear_field_flow_coefficient_remainder_contDiffOn hA hΩ hU hUΩ W hW hτ Φ hc hΦ i q
  have hs := norm_original_coefficient_scaled_adjoint_remainder_jet_le hA hΩ hU hUΩ
    W hW z hz i hτ Φ hc hΦ hx hforward hB hjet hsmall q n hnq
  have hs' : ‖iteratedFDeriv ℝ n
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) => F (z + ‖z‖ • p.1, p.2)) (0, x)‖ ≤
        M * ‖z‖ ^ (q + 1) := by
    convert hs using 1
    dsimp [M, C, F, Z, Y]
    ring
  have hh := norm_unscaled_coefficient_jet_le (hA.prod hU) hF z ⟨hz, hx⟩
    hzpos hznorm (mul_nonneg hM (pow_nonneg (norm_nonneg z) _)) n hs'
  calc
    ‖iteratedFDeriv ℝ n F (z, x)‖ ≤ (M * ‖z‖ ^ (q + 1)) * ‖z‖⁻¹ ^ n := hh
    _ = M * ‖z‖ ^ (q + 1 - n) := by
      rw [mul_assoc, inv_pow, ← pow_sub₀ ‖z‖ hzpos.ne' hnqpow]

end RothschildStein.G4
