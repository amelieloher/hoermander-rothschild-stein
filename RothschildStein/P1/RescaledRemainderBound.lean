-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesWeightedTaylor
public import RothschildStein.P1.KernelEstimatesChart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Each actual remainder coordinate has its full
weighted Taylor bound, including coordinates below the selected letter weight. -/
theorem exists_remainder_coordinate_bound (i : Fin k) (j : Fin (n + m))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ ξ ∈ K, ∀ u, kgauge C.G u ≤ r →
      ‖C.R [i] ξ u j‖ ≤ M * kgauge C.G u ^
        (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)).toNat := by
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.R [i] z.1 z.2 j) C.T :=
    (contDiff_apply ℝ ℝ j).comp_contDiffOn (C.remainder_smooth [i])
  obtain ⟨r, hr, hr1, M, hM⟩ := weighted_taylor_local C.G C.T C.isOpen_T _ hs K hK
    (fun ξ hξ => C.mem_T_zero (hKU hξ))
    (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)).toNat (by
      intro ξ hξ J hJ
      apply C.remainder_weight [i] (List.cons_ne_nil i []) ξ (hKU hξ) j J
      simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      omega)
  refine ⟨r, hr, hr1, |M|, abs_nonneg _, fun ξ hξ u hu => ?_⟩
  exact (hM ξ hξ u hu).trans
    (mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg (kgauge_nonneg C.G u) _))

/-- On every compact rescaled shell the entire
reflected remainder is one order smaller. No lower coordinate is discarded. -/
theorem exists_rescaled_remainder_coordinate_bound (i : Fin k) (j : Fin (n + m))
    {K S : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hS : IsCompact S) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ξ ∈ K, ∀ u ∈ S,
      ‖ε ^ (((w i : ℕ) : ℝ) - (C.G.weight j : ℝ)) * C.R [i] ξ (-C.G.dilate ε u) j‖
        ≤ A * ε := by
  obtain ⟨r, hr, _, M, hM, hbound⟩ := C.exists_remainder_coordinate_bound i j hK hKU
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
  intro ξ hξ u hu
  have hg : kgauge C.G (-C.G.dilate ε u) = ε * kgauge C.G u := by
    have hn : kgauge C.G (-C.G.dilate ε u) = kgauge C.G (C.G.dilate ε u) :=
      G2.gauge_neg C.G _
    rw [hn, kgauge_dilate C.G hε]
  have hv := hbound ξ hξ (-C.G.dilate ε u)
    (by rw [hg]; exact (mul_le_mul_of_nonneg_left (hρ u hu) hε.le).trans hεr)
  have hc : ‖C.R [i] ξ (-C.G.dilate ε u) j‖ ≤ M * (ε * R) ^ b := by
    refine hv.trans ?_
    rw [hg]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hε.le (kgauge_nonneg C.G u))
        (mul_le_mul_of_nonneg_left (hρ u hu) hε.le) b) hM
  change ‖ε ^ d * C.R [i] ξ (-C.G.dilate ε u) j‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hε d)]
  calc
    ε ^ d * ‖C.R [i] ξ (-C.G.dilate ε u) j‖ ≤ ε ^ d * (M * (ε * R) ^ b) :=
      mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hε.le _)
    _ = (M * R ^ b) * ε ^ (d + (b : ℝ)) := by
      rw [mul_pow, Real.rpow_add hε, Real.rpow_natCast]
      ring
    _ ≤ (M * R ^ b) * ε := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM (pow_nonneg hR.le _))
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hε hε1 hexp

end RothschildStein.P1.LiftedChart
