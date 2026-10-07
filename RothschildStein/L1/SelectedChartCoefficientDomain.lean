-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SelectedAuxiliaryBox
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- Actual selected and shifted box parameters remain inside
the fixed joint flow domain. The radius of that domain does not vary
with the application scale (BB pp. 520–521). -/
theorem selected_chart_parameters_mem_ball {q n s : ℕ}
    (w : Fin q → ℕ+) (B : Fin n → G4.ShortWord w s)
    {a b δ r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (ha1 : a ≤ 1) (hba : b ≤ a) (haδ : a < δ) (hr1 : r ≤ 1)
    (u : Fin n → ℝ) (v : Fin (Fintype.card (G4.ShortWord w s)) → ℝ)
    (hu : u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (a*r))
    (hv : v ∈ G4.weightedBox (fun j => G4.shortWeight w (G4.shortIndex w j)) (b*r)) :
    Fin.append u v ∈ ball 0 δ := by
  have hcoeff := G4.selectedAuxiliary_coefficients_le w B ha hb hr le_rfl hba u v hu hv
  have hnorm := G4.weighted_coefficients_norm_le
    (fun j => G4.shortWeight w (G4.selectedAuxiliaryIndex w B j)) (mul_nonneg ha hr)
    ((mul_le_mul_of_nonneg_right ha1 hr).trans (by simpa using hr1)) hcoeff
  rw [mem_ball,dist_zero_right]
  exact (hnorm.trans (mul_le_of_le_one_right ha hr1)).trans_lt haδ

end RothschildStein.L1
