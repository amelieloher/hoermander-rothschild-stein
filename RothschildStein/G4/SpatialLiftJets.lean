-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AffineJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Lifting a spatial field to parameter/initial-point space preserves
finite jet control with the explicit composition factorial
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_spatial_lift_jet_le {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} (hΩ : IsOpen Ω) (W : E → F)
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W Ω)
    (p : P) {x : E} (hx : x ∈ Ω) (n : ℕ) {B : ℝ}
    (hjet : ∀ j ≤ n, ‖iteratedFDeriv ℝ j W x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun q : P × E => W q.2) (p, x)‖ ≤ n.factorial * B := by
  let S : Set (P × E) := univ ×ˢ Ω
  have hS : IsOpen S := isOpen_univ.prod hΩ
  have hp : (p, x) ∈ S := ⟨mem_univ _, hx⟩
  have hproj : ContDiffOn ℝ (⊤ : ℕ∞) (Prod.snd : P × E → E) S :=
    contDiff_snd.contDiffOn
  have hh := norm_iteratedFDerivWithin_comp_le hW hproj (n := n) (by simp)
    hΩ.uniqueDiffOn hS.uniqueDiffOn (fun q hq => hq.2) hp
    (C := B) (D := 1)
    (fun j hj => by simpa only [iteratedFDerivWithin_of_isOpen _ hΩ hx] using hjet j hj)
    (fun j hj _ => by
      rw [iteratedFDerivWithin_of_isOpen _ hS hp, one_pow]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [Nat.add_comm 1 k]
      exact
        (norm_positive_jet_clm_le (ContinuousLinearMap.snd ℝ P E) (p, x) k).trans
          (ContinuousLinearMap.norm_snd_le ℝ P E))
  simpa only [iteratedFDerivWithin_of_isOpen _ hS hp, Function.comp_def, one_pow,
    mul_one] using hh

end RothschildStein.G4
