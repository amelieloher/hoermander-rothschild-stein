-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BufferedMappedRemainder
public import RothschildStein.G4.WeightedRemainderQuotients

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The buffered actual remainder has the signed frame weight.
The primitive jets provide the cofactor budget; initial suboptimality and
selected half-determinant persistence provide the denominator. No extra
inverse-suboptimality power is introduced (BB Lemma 9.49, p. 444). -/
theorem buffered_mapped_remainder_frame_weight_bound {k n s m h : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (I : Fin m → ShortWord w s)
    (x₀ : Fin n → ℝ) {R δ M : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ j, HasJetBound Ω (closedBall x₀ R) (X j) (h + 1 + s) M)
    (hδR : δ ≤ R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s)))
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φ
      ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2))
    (hΦ : ∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
      ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), t) ∈ closedBall x₀ R ∧
        HasDerivAt (fun v => Φ ((a, x), v))
          (∑ j, a j • shortField w X (I j) (Φ ((a, x), t))) t)
    (z : Fin m → ℝ) (hz : z ∈ ball 0 δ) (i : Fin m)
    {x : Fin n → ℝ} (hx : x ∈ ball x₀ (R / 8))
    (q : ℕ) (hq : q + 1 ≤ h) (horder : q + 1 = n * s + s)
    (hsmall : RothschildStein.G1.spatialJetRate (h + 1)
      ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial *
        (wordJetBase n (h + 1) s M ^ s) * ‖z‖) < 1)
    (Bframe : Fin n → ShortWord w s) (ℓ : Fin n) {e r t Δ : ℝ}
    (he : 0 ≤ e) (he1 : e ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (ht : 0 < t) (hΔ : 0 < Δ)
    (ha : ∀ j, |z j| ≤ (e * r) ^ (shortWeight w (I j) : ℕ))
    (hmax : ∃ C : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) C x|)
    (hB : IsSuboptimal (shortField w X) (shortWeight w) Bframe x t r)
    (hhalf : |frameDet (shortField w X) Bframe x| / 2 ≤
      |frameDet (shortField w X) Bframe (Φ ((z, x), 1))|) :
    let W := fun j => shortField w X (I j)
    let V := fun y => ∑ j, z j • W j y
    let J := wordJetBase n (h + 1) s M ^ s
    let H := wordJetBase n 0 s M ^ s
    let C := (2 ^ (h + 2) * ((m : ℝ) * 2 ^ (h + 1) * (h + 1).factorial * J)) ^ (q + 1) *
      ((h + 1).factorial * J)
    |frameCoefficient (shortField w X) Bframe (fun y =>
      fderiv ℝ (fun a => Φ ((a, x), 1)) z (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          ((VectorField.lieBracket ℝ V)^[j] (W i)) y) ℓ (Φ ((z, x), 1))| ≤
      (((n : ℝ) * n.factorial * (max H 1) ^ n) * (2 * C) / ((t / 2) * Δ)) *
        e ^ (n * s + s) *
          r ^ (((shortWeight w (Bframe ℓ) : ℕ) : ℤ) - ((shortWeight w (I i) : ℕ) : ℤ)) := by
  intro W V J H C
  have hw : ∀ u : ShortWord w s, (shortWeight w u : ℕ) ≤ s := fun u =>
    ((mem_shortWordFamily_iff w u.val).mp u.property).2
  have her : 0 ≤ e * r := mul_nonneg he hr.le
  have her1 : e * r ≤ 1 := (mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)
  have hznorm := weighted_coefficients_norm_le (fun j => shortWeight w (I j)) her her1 ha
  have hb := norm_buffered_mapped_coefficient_remainder_le hΩ w X hX I x₀ hR hδ hM hRΩ
    hjets hδR Φ hsmooth hΦ z hz (hznorm.trans her1) i hx q hq hsmall
  dsimp only at hb
  have hslice : ∀ j y, ((spatialBracketFamily
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ∑ u, p.1 u • W u p.2))^[j]
        (fun p => W i p.2)) (z, y) =
      ((VectorField.lieBracket ℝ V)^[j] (W i)) y := fun j y =>
    congrFun (spatialBracketFamily_iterate_slice _ _ z j) y
  have hsum : (∑ j ∈ Finset.range (q + 1),
      ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        ((spatialBracketFamily
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ∑ u, p.1 u • W u p.2))^[j]
            (fun p => W i p.2)) (z, Φ ((z, x), 1))) =
      ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        ((VectorField.lieBracket ℝ V)^[j] (W i)) (Φ ((z, x), 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hslice]
  rw [hsum] at hb
  have hJ : 0 ≤ J := pow_nonneg (wordJetBase_nonneg_and_le hM).1 _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnorm : ‖fderiv ℝ (fun a => Φ ((a, x), 1)) z (Pi.single i 1) -
      ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
        ((VectorField.lieBracket ℝ V)^[j] (W i)) (Φ ((z, x), 1))‖ ≤
        (2 * C) * (e * r) ^ (n * s + s) := by
    calc
      _ ≤ (2 * C) * ‖z‖ ^ (q + 1) := hb
      _ ≤ (2 * C) * (e * r) ^ (q + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hznorm _) (by positivity)
      _ = _ := by rw [horder]
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have hy : Φ ((z, x), 1) ∈ closedBall x₀ R :=
    ((hΦ z hz x hxin).2 1 (by constructor <;> norm_num)).1
  have hframe : ∀ (u : ShortWord w s) (l : Fin n), |shortField w X u (Φ ((z, x), 1)) l| ≤ H := by
    intro u l
    have hb0 := mappedShortField_jet_bound hΩ hRΩ w X hX (fun _ : Unit => u) hM
      (h := 0) (fun j => by simpa only [zero_add] using (hjets j).mono (by omega))
      () 0 (Nat.zero_le _) _ hy
    have hnorm0 : ‖shortField w X u (Φ ((z, x), 1))‖ ≤ H := by
      simpa only [norm_iteratedFDerivWithin_zero] using hb0
    have hcoord : |shortField w X u (Φ ((z, x), 1)) l| ≤
        ‖shortField w X u (Φ ((z, x), 1))‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (shortField w X u (Φ ((z, x), 1))) l
    exact hcoord.trans hnorm0
  have hdet0 := suboptimal_frameDet_lower_bound (shortWeight w) s hw Bframe ht hr hr1 hΔ.le hmax hB
  have hdet : (t / 2) * Δ * r ^ (n * s) ≤
      |frameDet (shortField w X) Bframe (Φ ((z, x), 1))| := by nlinarith
  exact frameCoefficient_weighted_remainder_le (shortField w X) Bframe _ ℓ _
    (by have := hw (Bframe ℓ); have := (shortWeight w (I i)).pos; omega)
    hframe (by positivity) he hr hr1 (half_pos ht) hΔ hdet hnorm

end RothschildStein.G4
