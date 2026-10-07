-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesChain

/-!
# Size and derivative bounds for the lifted kernel

From the weighted bounds of `Ψ` on the unit sphere (`HasWeightedBounds`), the chart chain rule and
the remainder weights, this file proves, uniformly on a compact `L ⊆ U`,
`|Ψ(ξ, η, Θ(η, ξ))| ≤ A d̃(ξ, η)^d` and
`|X̃_{i,ξ}[Ψ(ξ, η, Θ(η, ξ))]| ≤ M d̃(ξ, η)^(d - w_i)` (BB pp. 569–571, Prop 11.32).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)
variable {Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {d : ℤ}

/-- `ρ`-form of the size bound, uniform on a compact subset of `U`. -/
theorem exists_size_bound_gauge (hWB : HasWeightedBounds C.G d Ψ) {L : Set (Fin (n + m) → ℝ)}
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η ∈ L, ∀ ξ ∈ L, ξ ≠ η →
      |Ψ ξ η (C.Θ η ξ)| ≤ M * kgauge C.G (C.Θ η ξ) ^ d := by
  obtain ⟨R₀, hR₀⟩ := C.exists_gauge_bound hL hLU
  obtain ⟨M, hM0, hM⟩ := hWB L hL R₀
  refine ⟨M, hM0, fun η hη ξ hξ hne => ?_⟩
  exact (hM ξ hξ η hη (C.Θ η ξ) ((C.theta_eq_zero_iff (hLU hη) (hLU hξ)).not.mpr hne)
    (hR₀ η hη ξ hξ)).1

/-- Size bound `|K(ξ, η)| ≤ A d̃(ξ, η)^d` for `K = Ψ(ξ, η, Θ(η, ξ))`, uniform on a
compact subset of `U` (BB pp. 569–571, Prop 11.32; the chart comparison `ρ ≍ d̃` and the scaling to the unit sphere). -/
theorem exists_size_bound (hWB : HasWeightedBounds C.G d Ψ) {L : Set (Fin (n + m) → ℝ)}
    (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η →
      |Ψ ξ η (C.Θ η ξ)| ≤ A * ((C.dl ξ η).toReal) ^ d := by
  obtain ⟨M, hM0, hM⟩ := C.exists_size_bound_gauge hWB hL hLU
  refine ⟨M * C.gaugeConst ^ d.natAbs, by have := C.gaugeConst_pos; positivity, ?_⟩
  intro ξ hξ η hη hne
  have hne' : η ≠ ξ := hne.symm
  have hρ : 0 < kgauge C.G (C.Θ η ξ) :=
    kgauge_pos C.G ((C.theta_eq_zero_iff (hLU hη) (hLU hξ)).not.mpr hne)
  have hdl : C.dl ξ η = C.dl η ξ := C.dl_symm ξ η
  have hdpos : 0 < (C.dl η ξ).toReal := by
    refine ENNReal.toReal_pos ?_ (C.dl_ne_top (hLU hη) (hLU hξ))
    exact fun h => hne ((C.dl_eq_zero_iff (hLU hη) (hLU hξ)).mp h)
  have h1 : kgauge C.G (C.Θ η ξ) ≤ C.gaugeConst * (C.dl η ξ).toReal := by
    have := C.gauge_div_le_dl_toReal (hLU hη) (hLU hξ)
    rwa [div_le_iff₀ C.gaugeConst_pos, mul_comm] at this
  have h2 : (C.dl η ξ).toReal ≤ C.gaugeConst * kgauge C.G (C.Θ η ξ) := C.dl_toReal_le (hLU hη) (hLU hξ)
  have h3 := kzpow_le_const_mul C.one_le_gaugeConst hρ hdpos h1 h2 d
  rw [hdl]
  calc |Ψ ξ η (C.Θ η ξ)| ≤ M * kgauge C.G (C.Θ η ξ) ^ d := hM η hη ξ hξ hne
    _ ≤ M * (C.gaugeConst ^ d.natAbs * (C.dl η ξ).toReal ^ d) :=
        mul_le_mul_of_nonneg_left h3 hM0
    _ = M * C.gaugeConst ^ d.natAbs * (C.dl η ξ).toReal ^ d := by ring

/-- `ρ`-form of the derivative bound along `X̃_i`:
`|X̃_{i,ξ}[K(ξ, η)]| ≤ M ‖Θ(η, ξ)‖^(d - w_i)`, uniform on a compact subset of `U`. The `Y_i` term
and the remainder term `R_{[i],η}` (one weight better) are controlled by homogeneity and the
weighted Taylor bound; the parameter derivative preserves the degree (BB pp. 569–571). -/
theorem exists_derivative_bound_gauge (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hWB : HasWeightedBounds C.G d Ψ) {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) (i : Fin k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η ∈ L, ∀ z ∈ L, z ≠ η →
      |fderiv ℝ (fun ξ => Ψ ξ η (C.Θ η ξ)) z (C.Xl i z)| ≤
        M * kgauge C.G (C.Θ η z) ^ (d - ((w i : ℕ) : ℤ)) := by
  obtain ⟨R₀, hR₀⟩ := C.exists_gauge_bound hL hLU
  set Rm : ℝ := max R₀ 1 with hRmdef
  have hRm0 : 0 < Rm := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨M₁, hM₁0, hM₁⟩ := hWB L hL Rm
  have hXc : ContinuousOn (C.Xl i) L :=
    ((C.lift_smooth i).continuousOn).mono (hLU.trans C.U_subset_O)
  obtain ⟨MX, hMX⟩ := hL.exists_bound_of_continuousOn hXc
  obtain ⟨MY, hMY0, hMY⟩ := exists_field_homogeneous_bound C.G (C.Y i) (w i : ℕ)
    (C.model_field_smooth i).continuous (fun t ht u => C.model_field_homogeneous i t ht u)
  choose CR hCR0 hCR using fun j : Fin (n + m) => C.exists_remainder_bound hL hLU i j
  refine ⟨M₁ * |MX| * Rm ^ (w i : ℕ) + ∑ j, M₁ * (MY + CR j * Rm), ?_, ?_⟩
  · have : 0 ≤ ∑ j, M₁ * (MY + CR j * Rm) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg hM₁0 (add_nonneg hMY0 (mul_nonneg (hCR0 j) hRm0.le)))
    positivity
  intro η hη z hz hne
  have hηU := hLU hη
  have hzU := hLU hz
  have hu : C.Θ η z ≠ 0 := (C.theta_eq_zero_iff hηU hzU).not.mpr hne
  set u := C.Θ η z with hudef
  set ρ := kgauge C.G u with hρdef
  have hρ : 0 < ρ := kgauge_pos C.G hu
  have hρle : ρ ≤ Rm := (hR₀ η hη z hz).trans (le_max_left _ _)
  obtain ⟨-, hbA, hbC⟩ := hM₁ z hz η hη u hu hρle
  set P : ℝ := ρ ^ (d - ((w i : ℕ) : ℤ)) with hPdef
  have hP : 0 < P := zpow_pos hρ _
  rw [C.fderiv_kernel_field hΨ hηU hzU hne i]
  set Lm := fderiv ℝ (kernelUncurry Ψ) (z, η, u) with hLm
  -- first part
  have hfirst : |Lm (C.Xl i z, 0, 0)| ≤ M₁ * |MX| * Rm ^ (w i : ℕ) * P := by
    have h1 := hbA (C.Xl i z)
    have h2 : ‖C.Xl i z‖ ≤ |MX| := (hMX z hz).trans (le_abs_self _)
    have h3 : ρ ^ d = ρ ^ (w i : ℕ) * P := by
      rw [hPdef, ← zpow_natCast, ← zpow_add₀ hρ.ne']
      congr 1
      ring
    have h4 : ρ ^ (w i : ℕ) ≤ Rm ^ (w i : ℕ) := pow_le_pow_left₀ hρ.le hρle _
    calc |Lm (C.Xl i z, 0, 0)| ≤ M₁ * ρ ^ d * ‖C.Xl i z‖ := h1
      _ ≤ M₁ * ρ ^ d * |MX| := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = M₁ * |MX| * (ρ ^ (w i : ℕ) * P) := by rw [h3]; ring
      _ ≤ M₁ * |MX| * (Rm ^ (w i : ℕ) * P) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hP.le) (by positivity)
      _ = M₁ * |MX| * Rm ^ (w i : ℕ) * P := by ring
  -- second part
  have hsecond : |Lm (0, 0, C.Y i u + C.R [i] η u)| ≤ (∑ j, M₁ * (MY + CR j * Rm)) * P := by
    refine (abs_apply_third_le Lm _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hY := hMY u hu j
    have hR := hCR j η hη z hz hne
    have hc := hbC j
    have hsum : |(C.Y i u + C.R [i] η u) j| ≤
        MY * ρ ^ ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ)) +
          CR j * ρ ^ ((1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)) := by
      rw [Pi.add_apply]
      exact (abs_add_le _ _).trans (add_le_add hY hR)
    have e1 : ρ ^ ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ)) * ρ ^ (d - (C.G.weight j : ℤ)) = P := by
      rw [hPdef, ← zpow_add₀ hρ.ne']
      congr 1
      ring
    have e2 : ρ ^ ((1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)) *
        ρ ^ (d - (C.G.weight j : ℤ)) = ρ * P := by
      rw [hPdef, ← zpow_add₀ hρ.ne', show (1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ) +
        (d - (C.G.weight j : ℤ)) = (d - ((w i : ℕ) : ℤ)) + 1 by ring, zpow_add_one₀ hρ.ne']
      ring
    have hpow0 : 0 ≤ ρ ^ (d - (C.G.weight j : ℤ)) := (zpow_pos hρ _).le
    calc |(C.Y i u + C.R [i] η u) j| * |Lm (0, 0, Pi.single j 1)|
        ≤ (MY * ρ ^ ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ)) +
          CR j * ρ ^ ((1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ))) *
            (M₁ * ρ ^ (d - (C.G.weight j : ℤ))) :=
          mul_le_mul hsum hc (abs_nonneg _)
            (add_nonneg (mul_nonneg hMY0 (zpow_pos hρ _).le) (mul_nonneg (hCR0 j) (zpow_pos hρ _).le))
      _ = M₁ * MY * (ρ ^ ((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ)) * ρ ^ (d - (C.G.weight j : ℤ))) +
          M₁ * CR j * (ρ ^ ((1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)) *
            ρ ^ (d - (C.G.weight j : ℤ))) := by ring
      _ = M₁ * MY * P + M₁ * CR j * (ρ * P) := by rw [e1, e2]
      _ ≤ M₁ * (MY + CR j * Rm) * P := by
          have : ρ * P ≤ Rm * P := mul_le_mul_of_nonneg_right hρle hP.le
          nlinarith [mul_nonneg hM₁0 (hCR0 j)]
  calc |Lm (C.Xl i z, 0, 0) + Lm (0, 0, C.Y i u + C.R [i] η u)|
      ≤ |Lm (C.Xl i z, 0, 0)| + |Lm (0, 0, C.Y i u + C.R [i] η u)| := abs_add_le _ _
    _ ≤ M₁ * |MX| * Rm ^ (w i : ℕ) * P + (∑ j, M₁ * (MY + CR j * Rm)) * P :=
        add_le_add hfirst hsecond
    _ = (M₁ * |MX| * Rm ^ (w i : ℕ) + ∑ j, M₁ * (MY + CR j * Rm)) * P := by ring

end LiftedChart
end RothschildStein.P1
