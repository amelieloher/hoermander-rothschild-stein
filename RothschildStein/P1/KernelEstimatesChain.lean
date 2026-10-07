-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesChart
public import RothschildStein.P1.KernelEstimatesWeightedTaylor

/-!
# Chart chain rule and remainder weights

For `K(ξ, η) = Ψ(ξ, η, Θ(η, ξ))` the chart identity `bracket_approx` with `I = [i]` gives
`X̃_{i,ξ}[h(Θ(η, ξ))] = ((Y_i + R_{[i],η}) h)(Θ(η, ξ))` (BB p. 569, proof of Prop 11.32), and the
remainder weights give `|R_{[i],η}^j(u)| ≤ C ‖u‖^(w_j + 1 - w_i)` on compact parameter sets.
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
variable {Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- `ξ ↦ Ψ(ξ, η, Θ(η, ξ))` is `C¹` away from the pole. -/
theorem kernel_contDiffOn (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContDiffOn ℝ 1 (fun ξ => Ψ ξ η (C.Θ η ξ)) (C.U \ {η}) := by
  have hθ : ContDiffOn ℝ 1 (C.Θ η) C.U := (C.theta_contDiffOn_right hη).of_le (by simp)
  have hf : ContDiffOn ℝ 1 (fun ξ : Fin (n + m) → ℝ => (ξ, η, C.Θ η ξ)) (C.U \ {η}) :=
    (contDiffOn_id.prodMk (contDiffOn_const.prodMk hθ)).mono Set.sdiff_subset
  refine hΨ.comp hf (fun ξ hξ => ?_)
  exact (C.theta_eq_zero_iff hη hξ.1).not.mpr hξ.2

/-- Chain rule for `ξ ↦ Ψ(ξ, η, Θ(η, ξ))` at a point off the pole. -/
theorem hasFDerivAt_kernel (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η) :
    HasFDerivAt (fun ξ' => Ψ ξ' η (C.Θ η ξ'))
      ((fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ)).comp
        ((ContinuousLinearMap.id ℝ (Fin (n + m) → ℝ)).prod
          ((0 : (Fin (n + m) → ℝ) →L[ℝ] (Fin (n + m) → ℝ)).prod (fderiv ℝ (C.Θ η) ξ)))) ξ := by
  have hdiff : DifferentiableAt ℝ (C.Θ η) ξ :=
    ((C.theta_contDiffOn_right hη).differentiableOn (by simp)).differentiableAt
      (C.isOpen_U.mem_nhds hξ)
  have hA := (hasFDerivAt_id ξ).prodMk ((hasFDerivAt_const η ξ).prodMk hdiff.hasFDerivAt)
  have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff hη hξ).not.mpr hne
  exact (kernelUncurry_differentiableAt hΨ hu).hasFDerivAt.comp ξ hA

/-- The derivative of the kernel along the lifted field `X̃_i`:
`X̃_{i,ξ}[h(Θ(η, ξ))] = (Y_i + R_{[i],η}) h (Θ(η, ξ))` plus the parameter derivative
(BB p. 569). -/
theorem fderiv_kernel_field (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η) (i : Fin k) :
    fderiv ℝ (fun ξ' => Ψ ξ' η (C.Θ η ξ')) ξ (C.Xl i ξ) =
      fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ) (C.Xl i ξ, 0, 0) +
      fderiv ℝ (kernelUncurry Ψ) (ξ, η, C.Θ η ξ)
        (0, 0, C.Y i (C.Θ η ξ) + C.R [i] η (C.Θ η ξ)) := by
  rw [(C.hasFDerivAt_kernel hΨ hη hξ hne).fderiv]
  have hb := C.bracket_approx [i] (List.cons_ne_nil _ _) η hη ξ hξ
  have hb' : fderiv ℝ (C.Θ η) ξ (C.Xl i ξ) = C.Y i (C.Θ η ξ) + C.R [i] η (C.Θ η ξ) := hb
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply, hb']
  rw [← map_add]
  congr 1
  ext <;> simp

/-- Remainder weights: `|R_{[i],η}^j(Θ(η, ξ))| ≤ C ‖Θ(η, ξ)‖^(w_j + 1 - w_i)` uniformly for
`η, ξ` in a compact subset of `U` (the remainder has weight at least `1 - |I|`, via the weighted Taylor
bound; BB p. 548, Lemma 11.16). -/
theorem exists_remainder_bound {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U)
    (i : Fin k) (j : Fin (n + m)) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ η ∈ L, ∀ ξ ∈ L, ξ ≠ η →
      |C.R [i] η (C.Θ η ξ) j| ≤
        CR * kgauge C.G (C.Θ η ξ) ^ ((1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)) := by
  set b : ℤ := (1 : ℤ) - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ) with hbdef
  set F : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ := fun p => C.R [i] p.1 p.2 j with hF
  have hFsm : ContDiffOn ℝ (⊤ : ℕ∞) F C.T := (contDiffOn_pi.mp (C.remainder_smooth [i])) j
  have hcont : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      F (z.1, C.Θ z.1 z.2)) (L ×ˢ L) := by
    have h1 : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (z.1, C.Θ z.1 z.2))
        (L ×ˢ L) :=
      continuousOn_fst.prodMk (C.theta_continuousOn.mono (Set.prod_mono hLU hLU))
    exact hFsm.continuousOn.comp h1 (fun z hz => C.mem_T_theta (hLU hz.1) (hLU hz.2))
  obtain ⟨C₂, hC₂⟩ := (hL.prod hL).exists_bound_of_continuousOn hcont
  obtain ⟨R₀, hR₀⟩ := C.exists_gauge_bound hL hLU
  have hRm0 : 0 < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbound : ∀ η ∈ L, ∀ ξ ∈ L, |F (η, C.Θ η ξ)| ≤ |C₂| := by
    intro η hη ξ hξ
    have := hC₂ (η, ξ) ⟨hη, hξ⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hpos : ∀ η ∈ L, ∀ ξ ∈ L, ξ ≠ η → 0 < kgauge C.G (C.Θ η ξ) := by
    intro η hη ξ hξ hne
    exact kgauge_pos C.G ((C.theta_eq_zero_iff (hLU hη) (hLU hξ)).not.mpr hne)
  by_cases hb : b ≤ 0
  · refine ⟨|C₂| / (max R₀ 1) ^ b, by positivity, ?_⟩
    intro η hη ξ hξ hne
    have hρ := hpos η hη ξ hξ hne
    have hρle : kgauge C.G (C.Θ η ξ) ≤ max R₀ 1 := (hR₀ η hη ξ hξ).trans (le_max_left _ _)
    have h1 : (max R₀ 1) ^ b ≤ kgauge C.G (C.Θ η ξ) ^ b := kzpow_le_of_nonpos hρ hρle hb
    have h2 : |C₂| ≤ |C₂| / (max R₀ 1) ^ b * kgauge C.G (C.Θ η ξ) ^ b := by
      calc |C₂| = |C₂| / (max R₀ 1) ^ b * (max R₀ 1) ^ b := by
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact (hbound η hη ξ hξ).trans h2
  · obtain ⟨n₀, hn₀⟩ := Int.eq_ofNat_of_zero_le (le_of_lt (not_le.mp hb))
    have hjet : ∀ η ∈ L, ∀ J : List (Fin (n + m)), (J.map C.G.weight).sum < n₀ →
        rsPartial J (fun u => F (η, u)) 0 = 0 := by
      intro η hη J hJ
      have hWJ := C.remainder_weight [i] (List.cons_ne_nil _ _) η (hLU hη)
      have hww : (wordWeight w [i] : ℤ) = ((w i : ℕ) : ℤ) := by simp [wordWeight]
      refine hWJ j J ?_
      rw [hww]
      omega
    obtain ⟨r, hr0, hr1, C₁, hC₁⟩ := weighted_taylor_local C.G C.T C.isOpen_T F hFsm L hL
      (fun η hη => C.mem_T_zero (hLU hη)) n₀ hjet
    have hrb : 0 < r ^ b := zpow_pos hr0 b
    refine ⟨max (max C₁ 0) (|C₂| / r ^ b), le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
    intro η hη ξ hξ hne
    have hρ := hpos η hη ξ hξ hne
    have hpow : kgauge C.G (C.Θ η ξ) ^ b = kgauge C.G (C.Θ η ξ) ^ n₀ := by
      rw [hn₀, zpow_natCast]
    have hn : 0 ≤ kgauge C.G (C.Θ η ξ) ^ b := (zpow_pos hρ b).le
    by_cases hle : kgauge C.G (C.Θ η ξ) ≤ r
    · have := hC₁ η hη (C.Θ η ξ) hle
      rw [← hpow] at this
      exact this.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) hn)
    · have hge : r ^ b ≤ kgauge C.G (C.Θ η ξ) ^ b :=
        kzpow_le_of_nonneg hr0 (not_le.mp hle).le (by omega)
      have h2 : |C₂| ≤ |C₂| / r ^ b * kgauge C.G (C.Θ η ξ) ^ b := by
        calc |C₂| = |C₂| / r ^ b * r ^ b := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hge (by positivity)
      exact (hbound η hη ξ hξ).trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hn))

end LiftedChart

/-- A linear functional on the third slot is the sum of its values on coordinate vectors. -/
theorem abs_apply_third_le {N : ℕ}
    (L : ((Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)) →L[ℝ] ℝ) (v : Fin N → ℝ) :
    |L (0, 0, v)| ≤ ∑ j, |v j| * |L (0, 0, Pi.single j 1)| := by
  have : ((0 : Fin N → ℝ), (0 : Fin N → ℝ), v) =
      ∑ j, v j • ((0 : Fin N → ℝ), (0 : Fin N → ℝ), (Pi.single j (1 : ℝ) : Fin N → ℝ)) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.fst_sum, Prod.snd_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [map_smul, smul_eq_mul, abs_mul]

end RothschildStein.P1
