-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedPoleNormedTarget

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.P1

variable {N : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Finite smoothness across the parameter axis follows from explicit
weighted bounds on the off-axis iterated derivatives. The full derivative budget
is stated, so the lemma applies to each finite Taylor remainder separately. -/
theorem contDiffOn_of_weighted_pole_decay (G : HomogeneousGroup N)
    (W q m : ℕ) (hW : ∀ j, G.weight j ≤ W) (hq : 0 < q)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (H : P × (Fin N → ℝ) → B) (K : Set P) (hK : IsOpen K)
    (hzero : ∀ p ∈ K, H (p, 0) = 0)
    (hoff : ContDiffOn ℝ (⊤ : ℕ∞) H
      {z : P × (Fin N → ℝ) | z.1 ∈ K ∧ kgauge G z.2 < 1 ∧ z.2 ≠ 0})
    (hbound : ∀ j : ℕ, j ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ K, ∀ u : Fin N → ℝ, u ≠ 0 → kgauge G u ≤ 1 →
        ‖iteratedFDeriv ℝ j H (p, u)‖ ≤ C * kgauge G u ^ (W + q)) :
    ContDiffOn ℝ m H {z : P × (Fin N → ℝ) | z.1 ∈ K ∧ kgauge G z.2 < 1} := by
  induction m generalizing B with
  | zero =>
    have hopen : IsOpen {z : P × (Fin N → ℝ) |
        z.1 ∈ K ∧ kgauge G z.2 < 1 ∧ z.2 ≠ 0} :=
      (hK.preimage continuous_fst).inter
        ((isOpen_lt ((G2.continuous_gauge G).comp continuous_snd) continuous_const).inter
          (isOpen_compl_singleton.preimage continuous_snd))
    obtain ⟨C, hC, hb⟩ := hbound 0 le_rfl
    simp only [Nat.cast_zero, contDiffOn_zero]
    intro z hz
    by_cases hu : z.2 = 0
    · have he : z = (z.1, 0) := by ext <;> simp [hu]
      rw [he]
      apply ContinuousAt.continuousWithinAt
      apply HasFDerivAt.continuousAt (𝕜 := ℝ)
      apply hasFDerivAt_zero_of_weighted_norm_decay G W q hW hq H K z.1
        (hK.mem_nhds hz.1) hzero C hC
      intro p hp u hu
      by_cases h0 : u = 0
      · simp only [h0, hzero p hp, norm_zero]
        exact mul_nonneg hC (pow_nonneg (kgauge_nonneg G _) _)
      · simpa only [norm_iteratedFDeriv_zero] using hb p hp u h0 hu
    · exact ((hoff.continuousOn z ⟨hz.1, hz.2, hu⟩).continuousAt
        (hopen.mem_nhds ⟨hz.1, hz.2, hu⟩)).continuousWithinAt
  | succ m ih =>
    have hopen : IsOpen {z : P × (Fin N → ℝ) | z.1 ∈ K ∧ kgauge G z.2 < 1} :=
      (hK.preimage continuous_fst).inter
        (isOpen_lt ((G2.continuous_gauge G).comp continuous_snd) continuous_const)
    have hopenOff : IsOpen {z : P × (Fin N → ℝ) |
        z.1 ∈ K ∧ kgauge G z.2 < 1 ∧ z.2 ≠ 0} :=
      (hK.preimage continuous_fst).inter
        ((isOpen_lt ((G2.continuous_gauge G).comp continuous_snd) continuous_const).inter
          (isOpen_compl_singleton.preimage continuous_snd))
    obtain ⟨C, hC, hb⟩ := hbound 0 (Nat.zero_le _)
    have haxis : ∀ p ∈ K, HasFDerivAt H (0 : (P × (Fin N → ℝ)) →L[ℝ] B) (p, 0) := by
      intro p hp
      apply hasFDerivAt_zero_of_weighted_norm_decay G W q hW hq H K p
        (hK.mem_nhds hp) hzero C hC
      intro a ha u hu
      by_cases h0 : u = 0
      · simp only [h0, hzero a ha, norm_zero]
        exact mul_nonneg hC (pow_nonneg (kgauge_nonneg G _) _)
      · simpa only [norm_iteratedFDeriv_zero] using hb a ha u h0 hu
    have hDzero : ∀ p ∈ K, fderiv ℝ H (p, 0) = 0 := fun p hp => (haxis p hp).fderiv
    have hDoff : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ H)
        {z : P × (Fin N → ℝ) | z.1 ∈ K ∧ kgauge G z.2 < 1 ∧ z.2 ≠ 0} :=
      hoff.fderiv_of_isOpen hopenOff (by simp)
    have hDbound : ∀ j : ℕ, j ≤ m → ∃ C : ℝ, 0 ≤ C ∧
        ∀ p ∈ K, ∀ u : Fin N → ℝ, u ≠ 0 → kgauge G u ≤ 1 →
          ‖iteratedFDeriv ℝ j (fderiv ℝ H) (p, u)‖ ≤ C * kgauge G u ^ (W + q) := by
      intro j hj
      obtain ⟨C, hC, hb⟩ := hbound (j + 1) (Nat.succ_le_succ hj)
      refine ⟨C, hC, ?_⟩
      intro p hp u hu hρ
      simpa only [norm_iteratedFDeriv_fderiv] using hb p hp u hu hρ
    simp only [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := ℝ) (n := (m : WithTop ℕ∞)) (f := H) (hopen.uniqueDiffOn (𝕜 := ℝ))).mpr
    refine ⟨by simp, fderiv ℝ H, ih (fderiv ℝ H) hDzero hDoff hDbound, ?_⟩
    intro z hz
    apply HasFDerivAt.hasFDerivWithinAt
    by_cases hu : z.2 = 0
    · have he : z = (z.1, 0) := by ext <;> simp [hu]
      rw [he]
      exact (haxis z.1 hz.1).differentiableAt.hasFDerivAt
    · exact ((hoff.differentiableOn (by simp) z ⟨hz.1, hz.2, hu⟩).differentiableAt
        (hopenOff.mem_nhds ⟨hz.1, hz.2, hu⟩)).hasFDerivAt

end RothschildStein.P1
