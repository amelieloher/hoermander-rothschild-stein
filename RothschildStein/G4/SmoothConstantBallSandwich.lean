-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothShortBallBoxProvider
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4

/-- Actual ball-box charts convert every small auxiliary endpoint to a
constant short-control endpoint, uniformly on an interior buffer. -/
theorem exists_smooth_constant_ball_sandwich {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k+1) → ℕ+)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R A ρ : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 0 < A ∧ 0 < ρ ∧
      ∀ x ∈ closedBall z (R/16), ∀ r : ℝ, 0 < r → r ≤ ρ →
      {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ⊆
      {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (A*r)} := by
  classical
  obtain ⟨R, hR, hRΩ, a, b, r₀, D, κ, ha, _ha1, hb, _hba, _hb1,
    hr₀, _hr₀1, _hD, _hκ, _hnκ, Φ, hΦ⟩ :=
    exists_smooth_short_ball_box_provider hn hs w
      (t := 1/2) (by norm_num) (by norm_num) hΩ X hX hstep hz
  refine ⟨R, a/b, b*r₀, hR, hRΩ, div_pos ha hb, mul_pos hb hr₀, ?_⟩
  intro x hx r hr hrr y hy
  have hxΩ : x ∈ Ω := hRΩ (closedBall_subset_closedBall (by linarith) hx)
  obtain ⟨B, hB⟩ := exists_suboptimal_frame (shortField w X) (shortWeight w)
    (t := 1/2) (by norm_num) (div_pos hr hb) (exists_short_frame hstep hxΩ)
  have hscale : r/b ≤ r₀ := (div_le_iff₀ hb).mpr (by nlinarith)
  have hzero : (0 : Fin (Fintype.card (ShortWord w s)) → ℝ) ∈
      weightedBox (fun j => shortWeight w (shortIndex w j)) (b*(r/b)) := by
    intro j
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos hb (div_pos hr hb)) _
  obtain ⟨_h₁, _h₂, _h₃, _h₄, _h₅, hin, _hout, _hle, hzeroout, _rest⟩ :=
    hΦ x hx (r/b) (div_pos hr hb) hscale B hB 0 hzero
  have hbr : b*(r/b) = r := by field_simp
  have har : a*(r/b) = (a/b)*r := by ring
  have hy' : y ∈ {y | auxiliaryDistance (s := s) Ω w X x y <
      ENNReal.ofReal (b*(r/b))} := by simpa only [hbr] using hy
  simpa only [har] using hzeroout rfl (hin hy')
end RothschildStein.G4
