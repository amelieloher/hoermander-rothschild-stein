-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.OriginalCoefficientScaledRemainderJets
public import RothschildStein.G4.ParameterBracketReparametrization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The original coefficient derivative remainder is expressed
using the original coefficient-field adjoints, while its jets use normalized
coefficient coordinates. No parameter derivatives occur in the spatial
adjoint identity (BB Lemma 9.48, pp. 441–443). -/
theorem norm_original_coefficient_scaled_adjoint_remainder_jet_le {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set (Fin N → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) (hz : z ∈ A) (i : Fin m) {τ : ℝ} (hτ : 1 < τ)
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
    (q n : ℕ) (hnq : n + (q + 1) ≤ R) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
      fun p => ∑ j, p.1 j • W j p.2
    let Y : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => W i p.2
    let C := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ (q + 1) *
      ((R + 1).factorial * B) * ‖z‖ ^ (q + 1)
    ‖iteratedFDeriv ℝ n (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
      fderiv ℝ (fun a => Φ ((a, p.2), 1)) (z + ‖z‖ • p.1) (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) (z + ‖z‖ • p.1, Φ ((z + ‖z‖ • p.1, p.2), 1)))) (0, x)‖ ≤
      n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n := by
  intro Z Y C
  let a : (Fin m → ℝ) → (Fin m → ℝ) := fun p => z + ‖z‖ • p
  let Zr : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
    fun p => ∑ j, (z j + ‖z‖ * p.1 j) • W j p.2
  have hBracket : ∀ p k, ((spatialBracketFamily Zr)^[k] Y) p =
      ((spatialBracketFamily Z)^[k] Y) (a p.1, p.2) := by
    intro p k
    have hh := spatialBracketFamily_iterate_parameter_reparametrization a Z Y p k
    simpa only [a, Z, Zr, Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hh
  have hh := norm_original_coefficient_scaled_remainder_jet_le hA hΩ hU hUΩ W hW
    z hz i hτ Φ hc hΦ hx hforward hB hjet hsmall q n hnq
  change ‖iteratedFDeriv ℝ n (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
    fderiv ℝ (fun c => Φ ((c, p.2), 1)) (a p.1) (Pi.single i 1) -
      ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        (((spatialBracketFamily Zr)^[j] Y) (p.1, Φ ((a p.1, p.2), 1)))) (0, x)‖ ≤
    n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n at hh
  simp_rw [hBracket] at hh
  simpa only [a] using hh

end RothschildStein.G4
