-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameBounds
public import RothschildStein.G4.MatrixMagnitudeBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Cramer coordinates of an arbitrary remainder retain its norm
factor, with a numerical coefficient determined by the frame value bound
and the determinant lower bound (BB Lemma 9.49, p. 444). -/
theorem frameCoefficient_remainder_norm_le {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (x : Fin n → ℝ)
    {H β : ℝ} (hβ : 0 < β)
    (hZ : ∀ J k, |Z J x k| ≤ H) (hdet : β ≤ |frameDet Z B x|) :
    |frameCoefficient Z B V i x| ≤
      ((n : ℝ) * (n.factorial : ℝ) * (max H 1) ^ n) * ‖V x‖ / β := by
  classical
  have hH : 0 ≤ max H 1 := le_trans (by norm_num) (le_max_right H 1)
  have hP : 0 ≤ (n.factorial : ℝ) * (max H 1) ^ n := by positivity
  have hcoord : ∀ k, |frameCoefficient Z B (fun _ => Pi.single k 1) i x| ≤
      ((n.factorial : ℝ) * (max H 1) ^ n) / β := by
    intro k
    unfold frameCoefficient
    rw [abs_div]
    have hb := replacementDet_le_factorial_pow Z B (Pi.single k 1) i x hH
      (fun J l => (hZ J l).trans (le_max_left H 1))
      (fun l => by
        by_cases hl : l = k
        · subst l; simp
        · simp only [Pi.single_eq_of_ne hl, abs_zero]; exact hH)
    exact (div_le_div_of_nonneg_right hb (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hP hβ hdet)
  have hb := frameCoefficient_le_of_coordinate_bounds Z B V i x hcoord
  convert hb using 1
  ring

end RothschildStein.G4
