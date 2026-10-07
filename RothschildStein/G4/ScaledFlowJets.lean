-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ScaledFieldJets
public import RothschildStein.G1.ParameterJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Full parameter/initial-point jets of the actual rescaled flow
are less than two under an explicit primitive finite-jet smallness condition.
Joint smoothness follows from the parameter-flow theorem (BB Lemma 9.48, pp. 441–443). -/
theorem scaled_parameterFlow_jets_lt_two {m N R : ℕ}
    {A : Set (Fin m → ℝ)} {Ω : Set (Fin N → ℝ)}
    {U : Set ((Fin m → ℝ) × (Fin N → ℝ))}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w))
        (∑ i, (z i + ‖z‖ * p.1 i) • W i (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : (0, x) ∈ U) {t B : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hB : 0 ≤ B)
    (hjet : ∀ v ∈ uIcc 0 t, ∀ i, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j (W i) (Φ ((0, x), v))‖ ≤ B)
    (hsmall : RothschildStein.G1.spatialJetRate R
      ((m : ℝ) * 2 ^ R * R.factorial * B * ‖z‖) * |t| < 1) :
    ∀ n, 1 ≤ n → n ≤ R →
      ‖iteratedFDeriv ℝ n (fun p => Φ (p, t)) (0, x)‖ < 2 := by
  let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
    fun p => ∑ i, (z i + ‖z‖ * p.1 i) • W i p.2
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) := by
    apply ContDiffOn.sum
    intro i _
    exact (scaled_coefficient_contDiff z i).contDiffOn.smul
      ((hW i).comp contDiffOn_snd (fun p hp => hp.2))
  apply RothschildStein.G1.parameterFlow_spatialJets_bound hA hΩ hU hUA hZ hτ Φ hc hΦ
    R hx ht (by positivity) _ hsmall
  intro v hv j hj
  have hvI : v ∈ Ioo (-τ) τ :=
    (ordConnected_Ioo.uIcc_subset (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ⟩) ht) hv
  have hy : Φ ((0, x), v) ∈ Ω := ((hΦ (0, x) hx).2 v hvI).2
  apply (norm_scaled_field_jet_le hΩ W hW z hy hB (hjet v hv) j hj).trans
  gcongr
  norm_num

end RothschildStein.G4
