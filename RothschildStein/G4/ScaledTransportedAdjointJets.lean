-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TransportedFamilyJets
public import RothschildStein.G4.ParameterPreservingJets
public import RothschildStein.G4.ScaledAdjointJets
public import RothschildStein.G4.ScaledFlowJets
public import RothschildStein.G4.ParameterFlowSmoothness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Full joint jets of the ACTUAL transported rescaled adjoint
retain its coefficient-norm power. Forward/reverse flow jets and the common
open composition domain are derived from the actual ODE and primitive jets
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_scaled_flow_transported_adjoint_jet_le {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set ((Fin m → ℝ) × (Fin N → ℝ))}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) (i : Fin m) {τ : ℝ} (hτ : 0 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w))
        (∑ j, (z j + ‖z‖ * p.1 j) • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : (0, x) ∈ U) {s B : ℝ} (hs : s ∈ Ioo (-τ) τ)
    (hend : (0, Φ ((0, x), -s)) ∈ U) (hB : 0 ≤ B)
    (hjet : ∀ y ∈ Ω, ∀ j, ∀ l ≤ R + 1, ‖iteratedFDeriv ℝ l (W j) y‖ ≤ B)
    (hsmall : RothschildStein.G1.spatialJetRate (R + 1)
      ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B * ‖z‖) * |s| < 1)
    (k n : ℕ) (hnk : n + k ≤ R) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
      fun p => ∑ j, (z j + ‖z‖ * p.1 j) • W j p.2
    let Y := (spatialBracketFamily Z)^[k] (fun p => W i p.2)
    let C := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ k *
      ((R + 1).factorial * B) * ‖z‖ ^ k
    ‖iteratedFDeriv ℝ n
      (fun p => (fderiv ℝ (fun y => Φ ((p.1, y), s)) (Φ (p, -s)))
        (Y (p.1, Φ (p, -s)))) (0, x)‖ ≤ n.factorial * (2 ^ n * 2 * C) * 2 ^ n := by
  intro Z Y C
  have hZall := scaled_field_contDiffOn W hW z
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) :=
    hZall.mono (prod_mono (subset_univ A) Subset.rfl)
  have hjoint := parameterFlow_contDiffOn hA hΩ hU hUA hZ hτ Φ hc hΦ
  have hneg : -s ∈ Ioo (-τ) τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have htime : ∀ t ∈ Ioo (-τ) τ, ContDiffOn ℝ (⊤ : ℕ∞) (fun p => Φ (p, t)) U :=
    fun t ht => hjoint.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun p hp => ⟨hp, ht⟩)
  have hflowjets : ∀ y, (0, y) ∈ U → ∀ t ∈ Ioo (-τ) τ,
      |t| = |s| → ∀ l, 1 ≤ l → l ≤ R + 1 →
      ‖iteratedFDeriv ℝ l (fun p => Φ (p, t)) (0, y)‖ < 2 := by
    intro y hy t ht he
    apply scaled_parameterFlow_jets_lt_two hA hΩ hU hUA W hW z hτ Φ hc hΦ hy ht hB
    · intro v hv j l hl
      have hvI := ordConnected_Ioo.uIcc_subset
        (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ⟩) ht hv
      exact hjet _ ((hΦ (0, y) hy).2 v hvI).2 j l hl
    · simpa only [he] using hsmall
  let Q : ((Fin m → ℝ) × (Fin N → ℝ)) → ((Fin m → ℝ) × (Fin N → ℝ)) :=
    fun p => (p.1, Φ (p, -s))
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q U := contDiffOn_fst.prodMk (htime (-s) hneg)
  let V := U ∩ Q ⁻¹' U
  have hV : IsOpen V := hQ.continuousOn.isOpen_inter_preimage hU hU
  have hv : (0, x) ∈ V := ⟨hx, hend⟩
  have hYall : ContDiffOn ℝ (⊤ : ℕ∞) Y (univ ×ˢ Ω) :=
    spatialBracketFamily_iterate_contDiffOn (isOpen_univ.prod hΩ) hZall
      ((hW i).comp contDiffOn_snd (fun p hp => hp.2)) k
  have hYU : ContDiffOn ℝ (⊤ : ℕ∞) Y U :=
    hYall.mono (hUA.trans (prod_mono (subset_univ A) Subset.rfl))
  have hyΩ : Φ ((0, x), -s) ∈ Ω := ((hΦ (0, x) hx).2 (-s) hneg).2
  apply norm_transported_family_jet_le hV hU (htime s hs) hYU
    (hQ.mono inter_subset_left) (fun p hp => hp.2) hv (by norm_num)
    (show 0 ≤ C by dsimp [C]; positivity)
  · intro l hl hl'
    exact (hflowjets _ hend s hs rfl l hl (by omega)).le
  · intro l hl
    exact norm_scaled_adjoint_family_jet_le hΩ W hW z i hyΩ hB
      (hjet _ hyΩ) k l (by omega)
  · intro l hl hl'
    have hq := norm_parameter_preserving_map_jet_le
      ((htime (-s) hneg).contDiffAt (hU.mem_nhds hx)) hl (by norm_num : (1 : ℝ) ≤ 2)
      (hflowjets x hx (-s) hneg (abs_neg s) l hl (by omega)).le
    apply hq.trans
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl

end RothschildStein.G4
