-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.JointAdjointJets
public import RothschildStein.G4.ScaledFieldJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The rescaled actual coefficient field is jointly smooth on
parameter/spatial space (BB Lemma 9.48, pp. 441–443). -/
theorem scaled_field_contDiffOn {m N : ℕ} {Ω : Set (Fin N → ℝ)}
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω) (z : Fin m → ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
        ∑ i, (z i + ‖z‖ * p.1 i) • W i p.2) (univ ×ˢ Ω) := by
  apply ContDiffOn.sum
  intro i _
  exact (scaled_coefficient_contDiff z i).contDiffOn.smul
    ((hW i).comp contDiffOn_snd (fun p hp => hp.2))

/-- Full parameter/spatial jets of rescaled actual adjoints retain
one coefficient-norm factor per bracket, with explicit primitive finite-jet
constants (BB Lemma 9.48, pp. 441–443). -/
theorem norm_scaled_adjoint_family_jet_le {m N R : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) (i : Fin m) {x : Fin N → ℝ} (hx : x ∈ Ω)
    {B : ℝ} (hB : 0 ≤ B)
    (hjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (W i) x‖ ≤ B)
    (k n : ℕ) (hnk : n + k ≤ R) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
      fun p => ∑ j, (z j + ‖z‖ * p.1 j) • W j p.2
    ‖iteratedFDeriv ℝ n
      ((spatialBracketFamily Z)^[k] (fun p => W i p.2)) (0, x)‖ ≤
      (2 ^ (R + 1) * ((m : ℝ) * 2 ^ R * R.factorial * B)) ^ k *
        (R.factorial * B) * ‖z‖ ^ k := by
  intro Z
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (univ ×ˢ Ω) := scaled_field_contDiffOn W hW z
  have hY : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) => W i p.2) (univ ×ˢ Ω) :=
    (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  have hz : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Z (0, x)‖ ≤
      (m : ℝ) * 2 ^ R * R.factorial * B * ‖z‖ := by
    intro j hj
    apply (norm_scaled_field_jet_le hΩ W hW z hx hB hjet j hj).trans
    gcongr
    norm_num
  have hy : ∀ j ≤ R, ‖iteratedFDeriv ℝ j
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) => W i p.2) (0, x)‖ ≤ R.factorial * B := by
    intro j hj
    exact (norm_spatial_lift_jet_le hΩ (W i) (hW i) (0 : Fin m → ℝ) hx j
      (fun l hl => hjet i l (hl.trans hj))).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hB)
  have hh := norm_spatialBracketFamily_iterate_jet_le (isOpen_univ.prod hΩ)
    hZ hY (show (0, x) ∈ univ ×ˢ Ω from ⟨mem_univ _, hx⟩) hz hy k n hnk
  apply hh.trans_eq
  rw [← mul_assoc, mul_pow]
  ring

end RothschildStein.G4
