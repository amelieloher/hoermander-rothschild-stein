-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterTaylorTimeAgreement
public import RothschildStein.G4.ReparametrizedIntegralJets
public import RothschildStein.G4.ScaledTransportedAdjointJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- Full joint jets of the ACTUAL transported Taylor remainder
have the correct next-adjoint coefficient-norm power. Its exact integral
identity holds on a derived parameter neighborhood; no norm inequality is
differentiated (BB Lemma 9.48, pp. 442–443; NSW p. 127). -/
theorem norm_scaled_transported_taylor_remainder_jet_le_at_time {m N R : ℕ}
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
    (hend : ∀ s ∈ Icc (0 : ℝ) 1, (0, Φ ((0, x), -s)) ∈ U)
    {B : ℝ} (hB : 0 ≤ B)
    (hjet : ∀ y ∈ Ω, ∀ j, ∀ l ≤ R + 1, ‖iteratedFDeriv ℝ l (W j) y‖ ≤ B)
    (hsmall : RothschildStein.G1.spatialJetRate (R + 1)
      ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B * ‖z‖) < 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (q n : ℕ) (hnq : n + (q + 1) ≤ R) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
      fun p => ∑ j, (z j + ‖z‖ * p.1 j) • W j p.2
    let Y : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => W i p.2
    let C := (2 ^ (R + 2) * ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B)) ^ (q + 1) *
      ((R + 1).factorial * B) * ‖z‖ ^ (q + 1)
    ‖iteratedFDeriv ℝ n (fun p =>
      (fderiv ℝ (fun y => Φ ((p.1, y), t)) (Φ (p, -t))) (Y (p.1, Φ (p, -t))) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j * t ^ j / (j.factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) p)) (0, x)‖ ≤
      n.factorial * (2 ^ n * 2 * C) * 2 ^ n := by
  intro Z Y C
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) :=
    (scaled_field_contDiffOn W hW z).mono (prod_mono (subset_univ A) Subset.rfl)
  have hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω) :=
    (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  have he := parameterFlow_transported_taylor_remainder_eventuallyEq_at_time hA hΩ hU hUA
    Z Y hZ hY hτ Φ hc hΦ hx hend ht q
  let w : ℝ → ℝ := fun s => (q.factorial : ℝ)⁻¹ *
    ((1 - s) ^ q * t ^ (q + 1) * (-1 : ℝ) ^ (q + 1))
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by dsimp [w]; fun_prop
  have hwbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖w s‖ ≤ 1 := by
    intro s hs
    have hf : (1 : ℝ) ≤ q.factorial := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos q)
    have hinv : ‖(q.factorial : ℝ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact inv_le_one_of_one_le₀ hf
    have ha : ‖1 - s‖ ^ q ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
      exact pow_le_one₀ (by linarith [hs.2]) (by linarith [hs.1])
    have hb : ‖t‖ ^ (q + 1) ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact pow_le_one₀ ht.1 ht.2
    have hweight : ‖(1 - s) ^ q * t ^ (q + 1) * (-1 : ℝ) ^ (q + 1)‖ ≤ 1 := by
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
      exact (mul_le_mul ha hb (pow_nonneg (norm_nonneg _) _) (by norm_num)).trans_eq (one_mul _)
    exact (norm_mul_le _ _).trans ((mul_le_mul hinv hweight (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have he' := he.trans (Eventually.of_forall (fun p => by
    change (q.factorial : ℝ)⁻¹ • (∫ s in (0 : ℝ)..1,
      ((1 - s) ^ q * t ^ (q + 1) * (-1 : ℝ) ^ (q + 1)) •
        (fderiv ℝ (fun y => Φ ((p.1, y), s * t)) (Φ (p, -(s * t))))
          (((spatialBracketFamily Z)^[q + 1] Y) (p.1, Φ (p, -(s * t))))) =
      ∫ s in (0 : ℝ)..1, w s •
        (fderiv ℝ (fun y => Φ ((p.1, y), s * t)) (Φ (p, -(s * t))))
          (((spatialBracketFamily Z)^[q + 1] Y) (p.1, Φ (p, -(s * t))))
    rw [← intervalIntegral.integral_smul]
    simp only [smul_smul, w]))
  rw [(he'.iteratedFDeriv ℝ n).eq_of_nhds]
  let Ynext := (spatialBracketFamily Z)^[q + 1] Y
  have hZall := scaled_field_contDiffOn W hW z
  have hYall : ContDiffOn ℝ (⊤ : ℕ∞) Y (univ ×ˢ Ω) :=
    (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  have hNext : ContDiffOn ℝ (⊤ : ℕ∞) Ynext U :=
    (spatialBracketFamily_iterate_contDiffOn (isOpen_univ.prod hΩ) hZall hYall (q + 1)).mono
      (hUA.trans (prod_mono (subset_univ A) Subset.rfl))
  have hτ0 : 0 < τ := by linarith
  obtain ⟨hS, hP⟩ := actual_parameterFlow_transported_kernel_contDiffOn
    hA hΩ hU hUA hZ hτ0 Φ hc hΦ Ynext hNext
  let P : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ) :=
    fun v => (fderiv ℝ (fun y => Φ ((v.1.1, y), v.2)) (Φ (v.1, -v.2)))
      (Ynext (v.1.1, Φ (v.1, -v.2)))
  have hrt : ∀ r ∈ Icc (0 : ℝ) 1, r * t ∈ Icc (0 : ℝ) 1 := fun r hr =>
    ⟨mul_nonneg hr.1 ht.1, (mul_le_mul hr.2 ht.2 ht.1 (by norm_num)).trans_eq (one_mul _)⟩
  have hsI : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ Ioo (-τ) τ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hseg : ∀ r ∈ Icc (0 : ℝ) 1,
      ((0, x), r * t) ∈ (U ×ˢ Ioo (-τ) τ) ∩ {v | (v.1.1, Φ (v.1, -v.2)) ∈ U} :=
    fun r hr => ⟨⟨hx, hsI _ (hrt r hr)⟩, hend _ (hrt r hr)⟩
  apply norm_weighted_reparametrized_local_interval_integral_jet_le hS P hP
    (fun r => r * t) w (by fun_prop) hw (0, x) hseg hwbound n
  intro r hr
  apply norm_scaled_flow_transported_adjoint_jet_le hA hΩ hU hUA W hW z i hτ0
    Φ hc hΦ hx (hsI _ (hrt r hr)) (hend _ (hrt r hr)) hB hjet _ (q + 1) n hnq
  have hrate : 0 ≤ RothschildStein.G1.spatialJetRate (R + 1)
      ((m : ℝ) * 2 ^ (R + 1) * (R + 1).factorial * B * ‖z‖) := by
    unfold RothschildStein.G1.spatialJetRate
    positivity
  have habs : |r * t| ≤ 1 := by rw [abs_of_nonneg (hrt r hr).1]; exact (hrt r hr).2
  exact (mul_le_of_le_one_right hrate habs).trans_lt hsmall

end RothschildStein.G4
