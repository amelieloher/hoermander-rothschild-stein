-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.SuboptimalFrameVolumePolynomial
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.L1

/-- The exact volume-polynomial inequalities imply volume bounds
by the selected frame term, with its full inverse-suboptimality factor.
The geometric volume inequalities remain explicit (BB pp. 521–522). -/
theorem frame_term_volume_bounds_of_volumePolynomial_bounds
    {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (x : Fin n → ℝ) {t r c C : ℝ}
    (ht : 0 < t) (hr : 0 < r) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hB : G4.IsSuboptimal Z w B x t r)
    (A : Set (Fin n → ℝ))
    (hvol : ENNReal.ofReal (c * G4.volumePolynomial (fun D => G4.frameDet Z D x)
        (fun D : Fin n → ι => ∑ i, (w (D i) : ℕ)) r) ≤ volume A ∧
      volume A ≤ ENNReal.ofReal (C * G4.volumePolynomial (fun D => G4.frameDet Z D x)
        (fun D : Fin n → ι => ∑ i, (w (D i) : ℕ)) r)) :
    ENNReal.ofReal (c * (|G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ)))) ≤ volume A ∧
      volume A ≤ ENNReal.ofReal ((C * ((Fintype.card (Fin n → ι) : ℝ) / t)) *
        (|G4.frameDet Z B x| * r ^ (∑ i, (w (B i) : ℕ)))) := by
  obtain ⟨hlo, hhi⟩ := suboptimal_frame_volumePolynomial_bounds Z w B x ht hr hB
  refine ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlo hc)).trans hvol.1,
    hvol.2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hhi hC

end RothschildStein.L1
