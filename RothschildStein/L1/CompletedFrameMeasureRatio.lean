-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FrameTermVolumeBounds
public import RothschildStein.L1.MeasureRatioBounds
public import RothschildStein.L1.CompletedFrameRatio

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.L1

/-- The actual completed frame ratio is comparable in both
 directions with the ratio of measured balls, from the exact two-sided
 volume-polynomial inequalities. Constants retain the finite frame
 counts and suboptimality factors (BB pp. 521–522, (10.49)). -/
theorem completed_frame_measure_ratio_of_volumePolynomial_bounds
    {ι : Type*} [Fintype ι] {n m : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (Zlift : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (w : ι → ℕ+) (B : Fin n → ι) (J : Fin m → ι)
    (x : Fin n → ℝ) (ξ : Fin (n + m) → ℝ)
    {r t₀ t₁ c₀ C₀ c₁ C₁ : ℝ} (hr : 0 < r) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hB : G4.frameDet Z B x ≠ 0)
    (ho : G4.IsSuboptimal Z w B x t₀ r)
    (hl : G4.IsSuboptimal Zlift w (Fin.addCases B J) ξ t₁ r)
    (A : Set (Fin n → ℝ)) (Alift : Set (Fin (n + m) → ℝ))
    (hvol₀ : ENNReal.ofReal (c₀ * G4.volumePolynomial (fun D => G4.frameDet Z D x)
        (fun D : Fin n → ι => ∑ i, (w (D i) : ℕ)) r) ≤ volume A ∧
      volume A ≤ ENNReal.ofReal (C₀ * G4.volumePolynomial (fun D => G4.frameDet Z D x)
        (fun D : Fin n → ι => ∑ i, (w (D i) : ℕ)) r))
    (hvol₁ : ENNReal.ofReal (c₁ * G4.volumePolynomial (fun D => G4.frameDet Zlift D ξ)
        (fun D : Fin (n + m) → ι => ∑ i, (w (D i) : ℕ)) r) ≤ volume Alift ∧
      volume Alift ≤ ENNReal.ofReal (C₁ * G4.volumePolynomial (fun D => G4.frameDet Zlift D ξ)
        (fun D : Fin (n + m) → ι => ∑ i, (w (D i) : ℕ)) r)) :
    ENNReal.ofReal (c₁ / (C₀ * ((Fintype.card (Fin n → ι) : ℝ) / t₀))) *
      ENNReal.ofReal ((|G4.frameDet Zlift (Fin.addCases B J) ξ| / |G4.frameDet Z B x|) *
        r ^ G4.frameWeight w J) ≤ volume Alift / volume A ∧
    volume Alift / volume A ≤
      ENNReal.ofReal ((C₁ * ((Fintype.card (Fin (n + m) → ι) : ℝ) / t₁)) / c₀) *
        ENNReal.ofReal ((|G4.frameDet Zlift (Fin.addCases B J) ξ| / |G4.frameDet Z B x|) *
          r ^ G4.frameWeight w J) := by
  have hbase := frame_term_volume_bounds_of_volumePolynomial_bounds
    Z w B x ht₀ hr hc₀.le hC₀.le ho A hvol₀
  have hlift := frame_term_volume_bounds_of_volumePolynomial_bounds
    Zlift w (Fin.addCases B J) ξ ht₁ hr hc₁.le hC₁.le hl Alift hvol₁
  have hcard : 0 < (Fintype.card (Fin n → ι) : ℝ) := by
    have hp : 0 < Fintype.card (Fin n → ι) := Fintype.card_pos_iff.mpr ⟨B⟩
    exact_mod_cast hp
  have hcardLift : 0 < (Fintype.card (Fin (n + m) → ι) : ℝ) := by
    have hp : 0 < Fintype.card (Fin (n + m) → ι) :=
      Fintype.card_pos_iff.mpr ⟨Fin.addCases B J⟩
    exact_mod_cast hp
  have hscale : 0 < |G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ)) :=
    mul_pos (abs_pos.mpr hB) (pow_pos hr _)
  have hh := measure_ratio_bounds_of_positive_real_scales A Alift hscale hc₀
    (mul_pos hC₀ (div_pos hcard ht₀)) hc₁.le
    (mul_pos hC₁ (div_pos hcardLift ht₁)).le hbase hlift
  have he := completed_frame_volume_ratio Z Zlift w B J x ξ hr.ne' hB
  simp only [G4.frameWeight_eq_nat_sum, zpow_natCast] at he
  simpa only [G4.frameWeight_eq_nat_sum, zpow_natCast, ← he] using hh

end RothschildStein.L1
