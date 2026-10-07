-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterEndpointBuffer
public import RothschildStein.G4.ComposedLocalIntegralJets
public import RothschildStein.G4.ScaledTaylorTimeJets
public import RothschildStein.G4.JointTaylorRemainderKernel
public import RothschildStein.G4.ParameterPreservingJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Full jets of the actual Taylor remainder integral evaluated
at the moving time-one endpoint retain the next-adjoint coefficient power.
All reverse-buffer hypotheses follow from the forward segment
(BB Lemma 9.48, pp. 441–443; NSW p. 127). -/
theorem norm_scaled_endpoint_integrated_taylor_remainder_jet_le {m N R : ℕ}
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
    ‖iteratedFDeriv ℝ n (fun v => let p := (v.1, Φ (v, 1)); ∫ t in (0 : ℝ)..1,
      (fderiv ℝ (fun y => Φ ((p.1, y), t)) (Φ (p, -t))) (Y (p.1, Φ (p, -t))) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j * t ^ j / (j.factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) p)) (0, x)‖ ≤
      n.factorial * (n.factorial * (2 ^ n * 2 * C) * 2 ^ n) * 2 ^ n := by
  intro Z Y C
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) :=
    (scaled_field_contDiffOn W hW z).mono (prod_mono (subset_univ A) Subset.rfl)
  have hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω) :=
    (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  have hτ₀ : 0 < τ := by linarith
  have ht₁ : (1 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  let Q : ((Fin m → ℝ) × (Fin N → ℝ)) → ((Fin m → ℝ) × (Fin N → ℝ)) :=
    fun p => (p.1, Φ (p, 1))
  let y := Φ ((0, x), 1)
  have hy : (0, y) ∈ U := hforward 1 (by simp)
  have hrev : ∀ s ∈ Icc (0 : ℝ) 1, (0, Φ ((0, y), -s)) ∈ U :=
    parameterFlow_endpoint_reverse_segment hΩ hUA hZ hτ Φ hΦ hx hforward
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => Φ (p, 1)) U :=
    (parameterFlow_contDiffOn hA hΩ hU hUA hZ hτ₀ Φ hc hΦ).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun p hp => ⟨hp, ht₁⟩)
  have hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q U := contDiffOn_fst.prodMk hF
  obtain ⟨hS, hK⟩ := actual_parameterFlow_taylor_remainder_contDiffOn hA hΩ hU hUA
    Z Y hZ hY hτ₀ Φ hc hΦ q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply norm_composed_local_interval_integral_jet_le hU hS _ hK Q hQ hx
    (fun t ht => ⟨⟨hy, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hrev t ht⟩) n
    (M := n.factorial * (2 ^ n * 2 * C) * 2 ^ n) (D := 2)
  · intro t ht j hj
    have hh := norm_scaled_transported_taylor_remainder_jet_le_at_time hA hΩ hU hUA
      W hW z i hτ Φ hc hΦ hy hrev hB hjet hsmall ht q j (by omega)
    apply hh.trans
    gcongr <;> norm_num
  · intro j hj hjn
    have hfj := scaled_parameterFlow_jets_lt_two hA hΩ hU hUA W hW z hτ₀ Φ hc hΦ
      hx ht₁ hB
      (fun v hv l k hk => hjet _
        (((hΦ (0, x) hx).2 v ((ordConnected_Ioo.uIcc_subset
          (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ₀⟩) ht₁) hv)).2) l k hk)
      (by simpa using hsmall) j hj (by omega)
    have hqj := norm_parameter_preserving_map_jet_le
      (hF.contDiffAt (hU.mem_nhds hx)) hj (by norm_num : (1 : ℝ) ≤ 2) hfj.le
    exact hqj.trans (le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))

end RothschildStein.G4
