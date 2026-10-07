-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CoefficientEndpointAgreement
public import RothschildStein.G4.ScaledEndpointCoefficientJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- Full normalized jets of the ORIGINAL coefficient derivative
minus its signed endpoint bracket polynomial satisfy the actual finite-jet
remainder estimate. This remains valid at z=0 and uses no division by ‖z‖
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_original_coefficient_scaled_remainder_jet_le {m N R : ℕ}
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
      fun p => ∑ j, (z j + ‖z‖ * p.1 j) • W j p.2
    let Y : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => W i p.2
    let C := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ (q + 1) *
      ((R + 1).factorial * B) * ‖z‖ ^ (q + 1)
    ‖iteratedFDeriv ℝ n (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
      fderiv ℝ (fun a => Φ ((a, p.2), 1)) (z + ‖z‖ • p.1) (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) (p.1, Φ ((z + ‖z‖ • p.1, p.2), 1)))) (0, x)‖ ≤
      n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n := by
  intro Z Y C
  let a : (Fin m → ℝ) → (Fin m → ℝ) := fun p => z + ‖z‖ • p
  let L : ((Fin m → ℝ) × (Fin N → ℝ)) → ((Fin m → ℝ) × (Fin N → ℝ)) :=
    fun p => (a p.1, p.2)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hL : Continuous L := (ha.comp continuous_fst).prodMk continuous_snd
  let A' := a ⁻¹' A
  let U' := A' ×ˢ U
  have hA' : IsOpen A' := hA.preimage ha
  have hU' : IsOpen U' := hA'.prod hU
  have hUA' : U' ⊆ A' ×ˢ Ω := fun p hp => ⟨hp.1, hUΩ hp.2⟩
  let Ψ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ) :=
    fun p => Φ (L p.1, p.2)
  have hΨc : ContinuousOn Ψ (U' ×ˢ Ioo (-τ) τ) :=
    hc.comp ((hL.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp => ⟨hp.1, hp.2⟩)
  have hΨ : ∀ p ∈ U', Ψ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Ψ (p, w))
        (∑ j, (z j + ‖z‖ * p.1 j) • W j (Ψ (p, v))) v ∧ Ψ (p, v) ∈ Ω := by
    intro p hp
    simpa only [Ψ, L, a, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hΦ (L p) hp
  have hx' : (0, x) ∈ U' := by simpa [U', A', a] using And.intro hz hx
  have hfwd : ∀ s ∈ Icc (0 : ℝ) 1, (0, Ψ ((0, x), s)) ∈ U' := by
    intro s hs
    simpa [U', A', a, Ψ, L] using And.intro hz (hforward s hs)
  have hh := norm_scaled_endpoint_coefficient_integral_remainder_jet_le hA' hΩ hU' hUA'
    W hW z i hτ Ψ hΨc hΨ hx' hfwd hB hjet hsmall q n hnq
  have he := linear_field_flow_coefficient_endpoint_integral_eventuallyEq
    hA hΩ hU hUΩ W hW hτ Φ hc hΦ hz hx hforward i
  have hLt : Tendsto L (𝓝 (0, x)) (𝓝 (z, x)) := by
    simpa [L, a] using hL.continuousAt.tendsto (x := (0, x))
  have heL := he.comp_tendsto hLt
  have heR :
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
        fderiv ℝ (fun c => Φ ((c, p.2), 1)) (a p.1) (Pi.single i 1) -
          ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
            (((spatialBracketFamily Z)^[j] Y) (p.1, Ψ (p, 1)))) =ᶠ[𝓝 (0, x)]
      (fun v => let p := (v.1, Ψ (v, 1)); (∫ t in (0 : ℝ)..1,
        (fderiv ℝ (fun y => Ψ ((p.1, y), t)) (Ψ (p, -t))) (Y (p.1, Ψ (p, -t)))) -
          ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
            (((spatialBracketFamily Z)^[j] Y) p)) := by
    filter_upwards [heL] with p hp
    dsimp only [Function.comp_def, L] at hp
    change _ - _ = _ - _
    rw [hp]
  have hej := (heR.iteratedFDeriv ℝ n).eq_of_nhds
  dsimp only at hh hej
  rw [← hej] at hh
  simpa only [a, Ψ, L] using hh

end RothschildStein.G4
