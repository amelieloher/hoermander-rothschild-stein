-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SpatialPairingJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Full jets of an actual spatial Jacobian transported by a
joint map are controlled by finite jets of the forward map, transported
field, and reverse map (BB Lemma 9.48, pp. 441–443). -/
theorem norm_transported_family_jet_le {P E : Type*} {n : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U S : Set (P × E)} (hU : IsOpen U) (hS : IsOpen S)
    {F Y : P × E → E} {Q : P × E → P × E}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S)
    (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q U) (hQS : MapsTo Q U S)
    {p : P × E} (hp : p ∈ U) {M C D : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hFjet : ∀ j, 1 ≤ j → j ≤ n + 1 → ‖iteratedFDeriv ℝ j F (Q p)‖ ≤ M)
    (hYjet : ∀ j ≤ n, ‖iteratedFDeriv ℝ j Y (Q p)‖ ≤ C)
    (hQjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j Q p‖ ≤ D ^ j) :
    ‖iteratedFDeriv ℝ n
      (fun q => fderiv ℝ (fun x => F ((Q q).1, x)) (Q q).2 (Y (Q q))) p‖ ≤
      n.factorial * (2 ^ n * M * C) * D ^ n := by
  let B : P × E → E := fun q => fderiv ℝ (fun x => F (q.1, x)) q.2 (Y q)
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) B S :=
    (partial_spatial_fderiv_contDiffOn hS hF).clm_apply hY
  have hh := norm_iteratedFDerivWithin_comp_le hB hQ (n := n) (by simp)
    hS.uniqueDiffOn hU.uniqueDiffOn hQS hp (C := 2 ^ n * M * C) (D := D)
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen _ hS (hQS hp)]
      apply (norm_spatial_pairing_jet_le hS hF hY (hQS hp) hM
        (fun l hl hl' => hFjet l hl (by omega))
        (fun l hl => hYjet l (hl.trans hj))).trans
      gcongr
      norm_num)
    (fun j hj hj' => by
      simpa only [iteratedFDerivWithin_of_isOpen _ hU hp] using hQjet j hj hj')
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hp, Function.comp_def, B] using hh

end RothschildStein.G4
