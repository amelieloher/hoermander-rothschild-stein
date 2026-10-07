-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BufferedMappedRemainderCoordinates
public import RothschildStein.G4.UniformMappedTaylorCorrection
public import RothschildStein.G4.AdjointErrorCoordinates
public import RothschildStein.G4.GlobalReductionBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual coefficient derivative error is bounded by a finite
positive-order polynomial and its actual remainder. All constants are
chosen before the primitive fields and selected frame. Primitive jets and
actual determinant persistence are the only geometric inputs to the
coordinate estimate (BB Lemmas 9.48–9.49, pp. 441–445). -/
theorem exists_uniform_buffered_mapped_derivative_error_bound (k n s m h q : ℕ)
    (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ I : Fin m → ShortWord w s, ∀ x₀ : Fin n → ℝ, ∀ R δ : ℝ,
      0 < R → 0 < δ → closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max ((q + 1) * s) (h + 1 + s)) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      δ ≤ R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s)) →
      ∀ Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) →
      (∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
        ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), t) ∈ closedBall x₀ R ∧
          HasDerivAt (fun v => Φ ((a, x), v))
            (∑ j, a j • shortField w X (I j) (Φ ((a, x), t))) t) →
      ∀ (z : Fin m → ℝ), z ∈ ball 0 δ → ∀ i : Fin m,
      ∀ x : Fin n → ℝ, x ∈ ball x₀ (R / 8) →
      G1.spatialJetRate (h + 1) ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial *
        (wordJetBase n (h + 1) s M ^ s) * ‖z‖) < 1 →
      ∀ (B : Fin n → ShortWord w s) (ℓ : Fin n) (e r t D : ℝ),
      0 ≤ e → e ≤ 1 → 0 < r → r ≤ 1 → 0 < t → 0 ≤ D →
      (∀ j, |z j| ≤ (e * r) ^ (shortWeight w (I j) : ℕ)) →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      (|frameDet (shortField w X) B x| / 2 ≤
        |frameDet (shortField w X) B (Φ ((z, x), 1))|) →
      (∀ B' : Fin n → ShortWord w s, |frameDet (shortField w X) B' (Φ ((z, x), 1))| ≤
        D * r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) B') *
          |frameDet (shortField w X) B x|) →
      let J := wordJetBase n (h + 1) s M ^ s
      let H := wordJetBase n 0 s M ^ s
      let C₀ := (2 ^ (h + 2) * ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial * J)) ^ (q + 1) *
        ((h + 1).factorial * J)
      |frameCoefficient (shortField w X) B (fun y =>
        fderiv ℝ (fun a => Φ ((a, x), 1)) z (Pi.single i 1) - shortField w X (I i) y)
          ℓ (Φ ((z, x), 1))| ≤
        ((∑ j : Fin q, |(-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)| *
          (m : ℝ) ^ (j.val + 1) * C * D * e ^ (j.val + 1)) +
          (((n : ℝ) * n.factorial * (max H 1) ^ n) * (2 * C₀) / ((t / 2) * Δ)) *
            e ^ (n * s + s)) *
          r ^ (((shortWeight w (B ℓ) : ℕ) : ℤ) - ((shortWeight w (I i) : ℕ) : ℤ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_mapped_taylor_correction_bound k n s m q w M Δ hM hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ X hX hstep I x₀ R δ hR hδ hRΩ hjets hmax hδR Φ hsmooth hΦ
    z hz i x hx hsmall B ℓ e r t D he he1 hr hr1 ht hD ha hB hhalf hpersist J H C₀
  have hxK : x ∈ closedBall x₀ R := ball_subset_closedBall
    (ball_subset_ball (by linarith) hx)
  have hw : ∀ u : ShortWord w s, (shortWeight w u : ℕ) ≤ s := fun u =>
    ((mem_shortWordFamily_iff w u.val).mp u.property).2
  have hdet0 := suboptimal_frameDet_lower_bound (shortWeight w) s hw B ht hr hr1 hΔ.le (hmax x hxK) hB
  have hBx : frameDet (shortField w X) B x ≠ 0 := by
    have habs : 0 < |frameDet (shortField w X) B x| := (by positivity : 0 < t * Δ * r ^ (n * s)).trans_le hdet0
    exact abs_pos.mp habs
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have hy : Φ ((z, x), 1) ∈ closedBall x₀ R :=
    ((hΦ z hz x hxin).2 1 (by constructor <;> norm_num)).1
  let V := fun y => ∑ j, z j • shortField w X (I j) y
  let Dfield := fun _ : Fin n → ℝ => fderiv ℝ (fun a => Φ ((a, x), 1)) z (Pi.single i 1)
  have hc := hbound Ω (closedBall x₀ R) hΩ hRΩ X hX hstep
    (fun j => (hjets j).mono (le_max_left _ _))
    (fun y hy => determinantSquareSum_lower_bound (shortField w X) y hΔ.le (hmax y hy))
    I (I i) B ℓ x (Φ ((z, x), 1)) hy z e r D he he1 hr hr1 hD ha hBx hhalf hpersist
  have hrem := buffered_mapped_remainder_frame_weight_bound hΩ w X hX I x₀ hR hδ hM hRΩ
    (fun j => (hjets j).mono (le_max_right _ _)) hδR Φ hsmooth hΦ z hz i hx q hq horder
    hsmall B ℓ he he1 hr hr1 ht hΔ ha (hmax x hxK) hB hhalf
  dsimp only at hc hrem
  rw [adjoint_taylor_error_frameCoefficient (shortField w X) B Dfield V (shortField w X (I i)) q]
  exact ((abs_add_le _ _).trans (add_le_add hc hrem)).trans_eq (by ring)

end RothschildStein.G4
