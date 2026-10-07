-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferRemainderUniformBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MvPolynomial
open scoped BigOperators Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Uniformly in both compact endpoint parameters and every rescaled shell, the entire
transfer remainder is one order smaller. No lower coordinate is discarded. -/
theorem exists_uniform_rescaled_transfer_remainder_coordinate_bound
    (i : Fin k) (j : Fin (n + m))
    {K S : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hS : IsCompact S) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ξ ∈ K, ∀ η ∈ K, ∀ u ∈ S,
      ‖ε ^ (((w i : ℕ) : ℝ) - (C.G.weight j : ℝ)) * C.generatorTransferRemainder i ξ η (C.G.dilate ε u) j‖
        ≤ A * ε := by
  obtain ⟨r, hr, _, M, hM, hbound⟩ := C.exists_uniform_transfer_remainder_coordinate_bound i j hK hKU
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (G2.continuous_gauge C.G).continuousOn
  let R : ℝ := max 1 |B|
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hρ : ∀ u ∈ S, kgauge C.G u ≤ R := fun u hu =>
    (le_abs_self _).trans ((hB u hu).trans ((le_abs_self B).trans (le_max_right _ _)))
  let b : ℕ := (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)).toNat
  let d : ℝ := ((w i : ℕ) : ℝ) - (C.G.weight j : ℝ)
  have hexp : 1 ≤ d + (b : ℝ) := by
    have hi : (1 : ℤ) ≤ ((w i : ℕ) : ℤ) - (C.G.weight j : ℤ) + (b : ℤ) := by
      dsimp [b]
      omega
    dsimp only [d]
    exact_mod_cast hi
  refine ⟨M * R ^ b, mul_nonneg hM (pow_nonneg hR.le _), ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (show (0 : ℝ) < min 1 (r / R) from lt_min one_pos (div_pos hr hR)))]
    with ε hε hεsmall
  have hε1 : ε ≤ 1 := (hεsmall.trans_le (min_le_left _ _)).le
  have hεr : ε * R ≤ r := (le_div_iff₀ hR).mp
    (hεsmall.trans_le (min_le_right _ _)).le
  intro ξ hξ η hη u hu
  have hg : kgauge C.G (C.G.dilate ε u) = ε * kgauge C.G u := by
    exact kgauge_dilate C.G hε u
  have hv := hbound ξ hξ η hη (C.G.dilate ε u)
    (by rw [hg]; exact (mul_le_mul_of_nonneg_left (hρ u hu) hε.le).trans hεr)
  have hc : ‖C.generatorTransferRemainder i ξ η (C.G.dilate ε u) j‖ ≤ M * (ε * R) ^ b := by
    refine hv.trans ?_
    rw [hg]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hε.le (kgauge_nonneg C.G u))
        (mul_le_mul_of_nonneg_left (hρ u hu) hε.le) b) hM
  change ‖ε ^ d * C.generatorTransferRemainder i ξ η (C.G.dilate ε u) j‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hε d)]
  calc
    ε ^ d * ‖C.generatorTransferRemainder i ξ η (C.G.dilate ε u) j‖ ≤ ε ^ d * (M * (ε * R) ^ b) :=
      mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hε.le _)
    _ = (M * R ^ b) * ε ^ (d + (b : ℝ)) := by
      rw [mul_pow, Real.rpow_add hε, Real.rpow_natCast]
      ring
    _ ≤ (M * R ^ b) * ε := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM (pow_nonneg hR.le _))
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp


end RothschildStein.P1.LiftedChart
