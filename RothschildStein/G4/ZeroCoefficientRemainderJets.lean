-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CoefficientRemainderLocalPower
public import RothschildStein.G4.CoefficientRemainderSmoothness
public import RothschildStein.G3.FlatFrechetJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- All actual full joint jets of the original coefficient
remainder through the retained Taylor order vanish at zero coefficients.
The uniform local power error and actual smoothness justify flatness
(BB Lemma 9.48, pp. 441–443). -/
theorem linear_field_flow_coefficient_remainder_zero_jets {m N R : ℕ}
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
    ∀ n ≤ q, iteratedFDeriv ℝ n (fun p =>
      fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) (p.1, Φ (p, 1)))) (0, x) = 0 := by
  intro Z Y
  let C : ℝ := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ (q + 1) *
    ((R + 1).factorial * B)
  let F : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p =>
    fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1) -
      ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        (((spatialBracketFamily Z)^[j] Y) (p.1, Φ (p, 1)))
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ U) :=
    linear_field_flow_coefficient_remainder_contDiffOn hA hΩ hU hUΩ W hW hτ Φ hc hΦ i q
  let T : ((Fin m → ℝ) × (Fin N → ℝ)) → ((Fin m → ℝ) × (Fin N → ℝ)) :=
    fun p => (0, x) + p
  let f : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => F (T p)
  have hfc : ContDiffAt ℝ q f 0 := by
    have hs : ContDiffAt ℝ q F (T 0) := by
      simpa only [T, add_zero] using
        (hF.contDiffAt ((hA.prod hU).mem_nhds ⟨hz, hx⟩)).of_le (by simp)
    exact hs.comp 0 (contDiffAt_const.add contDiffAt_id)
  have hT : Tendsto T (𝓝 0) (𝓝 (0, x)) := by
    have hh : Continuous T := continuous_const.add continuous_id
    simpa only [T, add_zero] using hh.continuousAt.tendsto (x := 0)
  have he := linear_field_flow_coefficient_remainder_eventually_norm_le hA hΩ hU hUΩ
    W hW hz i hτ Φ hc hΦ hx hB hjet q hqR
  have heT := hT.eventually he
  have hb : ∀ᶠ p : (Fin m → ℝ) × (Fin N → ℝ) in 𝓝 0,
      ‖f p - 0‖ ≤ (2 * C) * ‖p‖ ^ (q + 1) := by
    have hC : 0 ≤ C := by dsimp [C]; positivity
    filter_upwards [heT] with p hp
    have hh : ‖f p‖ ≤ 2 * C * ‖p.1‖ ^ (q + 1) := by
      simpa only [f, F, T, Prod.fst_add, zero_add] using hp
    simp only [sub_zero]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg p.1) (norm_fst_le p) (q + 1)) (by positivity))
  intro n hn
  have hh := RothschildStein.G3.frechet_jets_eq_of_power_error hfc
    (contDiffAt_const (c := (0 : Fin N → ℝ))) hb n hn
  simpa [f, T, iteratedFDeriv_comp_add_left] using hh

end RothschildStein.G4
