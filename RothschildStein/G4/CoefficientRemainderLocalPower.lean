-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ZeroCoefficientFlow
public import RothschildStein.G4.ForwardSegmentNeighborhood
public import RothschildStein.G4.OriginalCoefficientScaledAdjointJets
public import RothschildStein.G1.MixedJetTimeScale

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- The actual coefficient derivative remainder has a uniform
power bound on one neighborhood of zero coefficients and the base initial
point. Forward buffers and rate smallness are derived, not assumed there
(BB Lemma 9.48, pp. 441–443). -/
theorem linear_field_flow_coefficient_remainder_eventually_norm_le {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set (Fin N → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (hz : (0 : Fin m → ℝ) ∈ A) (i : Fin m) {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w))
        (∑ j, p.1 j • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U)
    {B : ℝ} (hB : 0 ≤ B)
    (hjet : ∀ y ∈ Ω, ∀ j, ∀ l ≤ R + 1, ‖iteratedFDeriv ℝ l (W j) y‖ ≤ B)
    (q : ℕ) (hqR : q + 1 ≤ R) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
      fun p => ∑ j, p.1 j • W j p.2
    let Y : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => W i p.2
    let C := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ (q + 1) *
      ((R + 1).factorial * B)
    ∀ᶠ p in 𝓝 ((0 : Fin m → ℝ), x),
      ‖fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) (p.1, Φ (p, 1)))‖ ≤ 2 * C * ‖p.1‖ ^ (q + 1) := by
  intro Z Y C
  let D : ℝ := (m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B
  have hfwd : ∀ s ∈ Icc (0 : ℝ) 1, Φ ((0, x), s) ∈ U := by
    intro s hs
    rw [linear_field_flow_zero_coefficients W (show 0 < τ by linarith) Φ hΦ hz hx
      (show s ∈ Ioo (-τ) τ from ⟨by linarith [hs.1], by linarith [hs.2]⟩)]
    exact hx
  have he := parameterFlow_forward_segment_eventually (hA.prod hU) hU hτ Φ hc
    ⟨hz, hx⟩ hfwd
  have hrate : Continuous (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
      ‖p.1‖ * RothschildStein.G1.spatialJetRate (R + 1) D) := by fun_prop
  have hs : ∀ᶠ p : (Fin m → ℝ) × (Fin N → ℝ) in 𝓝 (0, x),
      ‖p.1‖ * RothschildStein.G1.spatialJetRate (R + 1) D < 1 :=
    hrate.continuousAt.eventually (Iio_mem_nhds (by simp))
  filter_upwards [he, hs] with p hp hsmall
  have hrate' : RothschildStein.G1.spatialJetRate (R + 1)
      ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B * ‖p.1‖) < 1 := by
    have heq : D * ‖p.1‖ = ‖p.1‖ * D := mul_comm _ _
    change RothschildStein.G1.spatialJetRate (R + 1) (D * ‖p.1‖) < 1
    rw [heq, RothschildStein.G1.spatialJetRate_mul_left]
    exact hsmall
  have hh := norm_original_coefficient_scaled_adjoint_remainder_jet_le hA hΩ hU hUΩ
    W hW p.1 hp.1.1 i hτ Φ hc hΦ hp.1.2 hp.2 hB hjet hrate' q 0 (by omega)
  dsimp only at hh
  simpa only [norm_iteratedFDeriv_zero, zero_smul, smul_zero, add_zero, pow_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, mul_one, C, Z, Y, mul_assoc] using hh

end RothschildStein.G4
