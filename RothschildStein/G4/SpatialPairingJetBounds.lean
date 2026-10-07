-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.JointSpatialBrackets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Primitive full jets give a quantitative bound for a spatial
Jacobian applied to a joint field family (BB pp. 441–443). -/
theorem norm_spatial_pairing_jet_le {P E : Type*} {n : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (P × E)} (hS : IsOpen S) {F Y : P × E → E}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S)
    {p : P × E} (hp : p ∈ S) {M C : ℝ} (hM : 0 ≤ M)
    (hFjet : ∀ j, 1 ≤ j → j ≤ n + 1 → ‖iteratedFDeriv ℝ j F p‖ ≤ M)
    (hYjet : ∀ j ≤ n, ‖iteratedFDeriv ℝ j Y p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ (fun x => F (q.1, x)) q.2 (Y q)) p‖ ≤
      2 ^ n * M * C := by
  apply (norm_joint_spatial_derivative_jet_le hS hY hF hp n).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * M * C := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      gcongr
      · exact hFjet (j + 1) (by omega) (by omega)
      · exact hYjet (n - j) (Nat.sub_le n j)
    _ = _ := by
      simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      rfl

end RothschildStein.G4
