-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ScaledCoefficientJets
public import RothschildStein.G4.SpatialLiftJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Full jets of the actual rescaled coefficient field retain a
coefficient-norm factor, with an explicit finite primitive-jet constant
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_scaled_field_jet_le {m N R : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (W i) Ω)
    (z : Fin m → ℝ) {x : Fin N → ℝ} (hx : x ∈ Ω)
    {B : ℝ} (hB : 0 ≤ B)
    (hjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (W i) x‖ ≤ B)
    (n : ℕ) (hn : n ≤ R) :
    ‖iteratedFDeriv ℝ n
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
        ∑ i, (z i + ‖z‖ * p.1 i) • W i p.2) (0, x)‖ ≤
      (m : ℝ) * 2 ^ n * R.factorial * B * ‖z‖ := by
  let S : Set ((Fin m → ℝ) × (Fin N → ℝ)) := univ ×ˢ Ω
  have hS : IsOpen S := isOpen_univ.prod hΩ
  have hp : (0, x) ∈ S := ⟨mem_univ _, hx⟩
  have hw : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) => W i p.2) S :=
    fun i => (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  have hi : ∀ i, ‖iteratedFDeriv ℝ n
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
        (z i + ‖z‖ * p.1 i) • W i p.2) (0, x)‖ ≤
      2 ^ n * ‖z‖ * (R.factorial * B) := by
    intro i
    have hh := norm_iteratedFDerivWithin_smul_le
      (scaled_coefficient_contDiff z i).contDiffOn (hw i) hS.uniqueDiffOn hp
      (n := n) (by simp)
    simp only [iteratedFDerivWithin_of_isOpen _ hS hp] at hh
    apply hh.trans
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ‖z‖ * (R.factorial * B) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : n - j ≤ R := (Nat.sub_le n j).trans hn
        have hv := norm_spatial_lift_jet_le hΩ (W i) (hW i) (0 : Fin m → ℝ) hx
          (n - j) (fun l hl => hjet i l (hl.trans hjn))
        have hv' : ‖iteratedFDeriv ℝ (n - j)
            (fun p : (Fin m → ℝ) × (Fin N → ℝ) => W i p.2) (0, x)‖ ≤ R.factorial * B :=
          hv.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hjn) hB)
        gcongr
        · exact norm_scaled_coefficient_jet_le z i x j

      _ = _ := by
        simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rfl
  have hs : ∀ i, ContDiffAt ℝ n
      (fun p : (Fin m → ℝ) × (Fin N → ℝ) =>
        (z i + ‖z‖ * p.1 i) • W i p.2) (0, x) := fun i =>
    (((scaled_coefficient_contDiff z i).contDiffOn.smul (hw i)).contDiffAt
      (hS.mem_nhds hp)).of_le (by simp)
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => hs i)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin m, 2 ^ n * ‖z‖ * (R.factorial * B) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end RothschildStein.G4
