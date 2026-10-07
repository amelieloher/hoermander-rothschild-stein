-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedTaylorParameters
public import RothschildStein.P1.LocalCoefficientExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.P1
variable {N : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [LocallyCompactSpace P] [FiniteDimensional ℝ P]

/-- Weighted Taylor bounds are uniform on
compact sets of both endpoint parameters. Extension is used only
near the zero model coordinate (BB Lemma 11.16 and Remark 11.17,
p. 548, applied in the critical transfer proof on p. 557). -/
theorem weighted_taylor_local_transfer_parameters (G : HomogeneousGroup N)
    (T : Set (P × (Fin N → ℝ))) (hT : IsOpen T)
    (A : P × (Fin N → ℝ) → ℝ) (hA : ContDiffOn ℝ (⊤ : ℕ∞) A T)
    (K : Set P) (hK : IsCompact K) (hKT : ∀ p ∈ K, (p, (0 : Fin N → ℝ)) ∈ T)
    (b : ℕ) (hjet : ∀ p ∈ K, ∀ J : List (Fin N), (J.map G.weight).sum < b →
      rsPartial J (fun u => A (p,u)) 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ∀ u : Fin N → ℝ,
      kgauge G u ≤ r → ‖A (p,u)‖ ≤ M * kgauge G u ^ b := by
  obtain ⟨B, hB, ε, hε, he⟩ := exists_global_extension_generic_parameter T hT A hA K hK hKT
  have hjB := extension_preserves_weighted_jets G A B K ε hε he b hjet
  obtain ⟨M, hM⟩ := weighted_taylor_generic_parameter G b B hB K hK hjB
  refine ⟨min 1 ε, lt_min one_pos hε, min_le_left _ _, |M|, abs_nonneg _, ?_⟩
  intro p hp u hu
  have hρ : kgauge G u ≤ 1 := hu.trans (min_le_left _ _)
  have hnorm : ‖u‖ ≤ ε := (norm_le_kgauge G hρ).trans (hu.trans (min_le_right _ _))
  rw [← he p hp u hnorm, Real.norm_eq_abs]
  exact (hM p hp u hρ).trans
    (mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg (kgauge_nonneg G u) _))

end RothschildStein.P1
