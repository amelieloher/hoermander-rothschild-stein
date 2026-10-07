-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BufferedMappedDerivativeError
public import RothschildStein.G4.MappedFlowFramePersistence
public import RothschildStein.G4.AdjointErrorSmallness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- One numerical weighted coefficient radius makes the actual
unit-time derivative error small in every suboptimal frame, uniformly
before the primitive fields, flow and selected frame are given. Both
persistence and the jet bootstrap condition are discharged by proved
providers (BB Lemma 9.49, pp. 441–445). -/
theorem exists_uniform_buffered_mapped_derivative_smallness (k n s m h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) (M Δ R δ t κ : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) (hδ : 0 < δ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hκ : 0 < κ)
    (hδR : δ ≤ R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s))) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧ e < δ ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ I : Fin m → ShortWord w s, ∀ x₀ : Fin n → ℝ, closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) →
      (∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
        ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), τ) ∈ closedBall x₀ R ∧
          HasDerivAt (fun v => Φ ((a, x), v))
            (∑ j, a j • shortField w X (I j) (Φ ((a, x), τ))) τ) →
      ∀ (B : Fin n → ShortWord w s) x, x ∈ ball x₀ (R / 8) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ z : Fin m → ℝ, (∀ j, |z j| ≤ (e * r) ^ (shortWeight w (I j) : ℕ)) →
      (|frameDet (shortField w X) B (Φ ((z, x), 1)) - frameDet (shortField w X) B x| ≤
        |frameDet (shortField w X) B x| / 2) ∧
      ∀ (i : Fin m) (ℓ : Fin n),
      |frameCoefficient (shortField w X) B (fun y =>
        fderiv ℝ (fun a => Φ ((a, x), 1)) z (Pi.single i 1) - shortField w X (I i) y)
          ℓ (Φ ((z, x), 1))| ≤
        κ * r ^ (((shortWeight w (B ℓ) : ℕ) : ℤ) - ((shortWeight w (I i) : ℕ) : ℤ)) := by
  obtain ⟨D, hD, hpersist⟩ := exists_uniform_mapped_flow_frame_persistence
    k n s m δ hδ hn hs w M Δ hM hΔ
  obtain ⟨e₀, he₀, he₀1, he₀t, he₀δ, hflowpersist⟩ := hpersist t ht ht1
  obtain ⟨C, hC, herror⟩ := exists_uniform_buffered_mapped_derivative_error_bound
    k n s m h q horder hq w M Δ hM hΔ
  let J := wordJetBase n (h + 1) s M ^ s
  let H := wordJetBase n 0 s M ^ s
  let C₀ := (2 ^ (h + 2) * ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial * J)) ^ (q + 1) *
    ((h + 1).factorial * J)
  let A := (((n : ℝ) * n.factorial * (max H 1) ^ n) * (2 * C₀) / ((t / 2) * Δ))
  let Bjet := (m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial * J
  let c : Fin q → ℝ := fun j => |(-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)| *
    (m : ℝ) ^ (j.val + 1) * C * (D * t⁻¹ ^ n)
  have hJ : 0 ≤ J := pow_nonneg (wordJetBase_nonneg_and_le hM).1 _
  have hBjet : 0 ≤ Bjet := by dsimp [Bjet]; positivity
  obtain ⟨e, he, he1, hee₀, hsmall⟩ := exists_adjoint_error_and_jet_smallness
    q (n * s + s) (h + 1) (by omega) c A Bjet κ e₀ hBjet hκ he₀
  refine ⟨e, he, he1, hee₀.trans he₀t, hee₀.trans_lt he₀δ, ?_⟩
  intro Ω hΩ X hX hstep I x₀ hRΩ hjets hmax Φ hsmooth hΦ B x hx r hr hr1 hB z ha
  have her : 0 ≤ e * r := mul_nonneg he.le hr.le
  have her1 : e * r ≤ 1 := (mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)
  have hznorm := weighted_coefficients_norm_le (fun j => shortWeight w (I j)) her her1 ha
  have hze : ‖z‖ ≤ e := hznorm.trans (mul_le_of_le_one_right he.le hr1)
  have hz : z ∈ ball 0 δ := by
    rw [mem_ball, dist_zero_right]
    exact hze.trans_lt (hee₀.trans_lt he₀δ)
  have ha₀ : ∀ j, |z j| ≤ (e₀ * r) ^ (shortWeight w (I j) : ℕ) := fun j =>
    (ha j).trans (pow_le_pow_left₀ her (mul_le_mul_of_nonneg_right hee₀ hr.le) _)
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have hUK : ball x₀ (R / 4) ⊆ closedBall x₀ R :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
  obtain ⟨hselected, hother⟩ := hflowpersist Ω (closedBall x₀ R) hΩ hRΩ X hX hstep
    (fun j => (hjets j).mono (le_max_left _ _)) hmax I (ball x₀ (R / 4)) hUK
    Φ hsmooth hΦ B x hxin r hr hr1 hB z ha₀
  have hhalf : |frameDet (shortField w X) B x| / 2 ≤
      |frameDet (shortField w X) B (Φ ((z, x), 1))| := by
    have htri : |frameDet (shortField w X) B x| ≤
        |frameDet (shortField w X) B (Φ ((z, x), 1)) - frameDet (shortField w X) B x| +
          |frameDet (shortField w X) B (Φ ((z, x), 1))| := by
      simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le
        (frameDet (shortField w X) B x - frameDet (shortField w X) B (Φ ((z, x), 1)))
        (frameDet (shortField w X) B (Φ ((z, x), 1)))
    linarith
  have hrate : G1.spatialJetRate (h + 1) (Bjet * ‖z‖) < 1 := by
    have hL : 0 ≤ G1.spatialJetRate (h + 1) Bjet := by
      dsimp [G1.spatialJetRate]
      exact Finset.sum_nonneg (fun j _ => by positivity)
    have hle : G1.spatialJetRate (h + 1) (Bjet * ‖z‖) ≤
        G1.spatialJetRate (h + 1) (Bjet * e) := by
      rw [mul_comm Bjet ‖z‖, mul_comm Bjet e, G1.spatialJetRate_mul_left (h + 1) ‖z‖ Bjet,
        G1.spatialJetRate_mul_left (h + 1) e Bjet]
      exact mul_le_mul_of_nonneg_right hze hL
    exact hle.trans_lt (hsmall e he.le le_rfl).2
  refine ⟨hselected, ?_⟩
  intro i ℓ
  have hb := herror Ω hΩ X hX hstep I x₀ R δ hR hδ hRΩ
    (fun j => (hjets j).mono (le_max_right _ _)) hmax hδR Φ hsmooth hΦ z hz i x hx
    hrate B ℓ e r t (D * t⁻¹ ^ n) he.le he1 hr hr1 ht (by positivity) ha hB hhalf hother
  dsimp only at hb
  have hP := (hsmall e he.le le_rfl).1.le
  exact hb.trans (mul_le_mul_of_nonneg_right hP (zpow_nonneg hr.le _))

end RothschildStein.G4
