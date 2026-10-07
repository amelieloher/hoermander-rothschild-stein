-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ScaledEndpointTaylorJets
public import RothschildStein.G4.IntegratedTaylorPolynomialAgreement

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- Full jets of the actual transported coefficient integral minus
the signed bracket polynomial at the moving endpoint retain the correct
next-adjoint coefficient power (BB Lemma 9.48, pp. 441–443). -/
theorem norm_scaled_endpoint_coefficient_integral_remainder_jet_le {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set ((Fin m → ℝ) × (Fin N → ℝ))}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) (i : Fin m) {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w))
        (∑ j, (z j + ‖z‖ * p.1 j) • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : (0, x) ∈ U)
    (hforward : ∀ s ∈ Icc (0 : ℝ) 1, (0, Φ ((0, x), s)) ∈ U)
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
    ‖iteratedFDeriv ℝ n (fun v => let p := (v.1, Φ (v, 1)); (∫ t in (0 : ℝ)..1,
      (fderiv ℝ (fun y => Φ ((p.1, y), t)) (Φ (p, -t))) (Y (p.1, Φ (p, -t)))) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) p)) (0, x)‖ ≤
      n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n := by
  intro Z Y C
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) :=
    (scaled_field_contDiffOn W hW z).mono (prod_mono (subset_univ A) Subset.rfl)
  have hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω) :=
    (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  let Q : ((Fin m → ℝ) × (Fin N → ℝ)) → ((Fin m → ℝ) × (Fin N → ℝ)) :=
    fun p => (p.1, Φ (p, 1))
  have hy : Q (0, x) ∈ U := hforward 1 (by simp)
  have hrev : ∀ s ∈ Icc (0 : ℝ) 1, (0, Φ (Q (0, x), -s)) ∈ U :=
    parameterFlow_endpoint_reverse_segment hΩ hUA hZ hτ Φ hΦ hx hforward
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => Φ (p, 1)) U :=
    (parameterFlow_contDiffOn hA hΩ hU hUA hZ (show 0 < τ by linarith) Φ hc hΦ).comp
      (contDiffOn_id.prodMk contDiffOn_const)
      (fun p hp => ⟨hp, ⟨by linarith, hτ⟩⟩)
  have hQ : ContinuousAt Q (0, x) :=
    (contDiffOn_fst.prodMk hF).continuousOn.continuousAt (hU.mem_nhds hx)
  have he := parameterFlow_integrated_taylor_remainder_eventuallyEq hA hΩ hU hUA
    Z Y hZ hY hτ Φ hc hΦ hy hrev q
  have heQ := he.comp_tendsto hQ.tendsto
  dsimp only [Function.comp_def, Q] at heQ
  dsimp only
  rw [← (heQ.iteratedFDeriv ℝ n).eq_of_nhds]
  exact norm_scaled_endpoint_integrated_taylor_remainder_jet_le hA hΩ hU hUA
    W hW z i hτ Φ hc hΦ hx hforward hB hjet hsmall q n hnq

end RothschildStein.G4
