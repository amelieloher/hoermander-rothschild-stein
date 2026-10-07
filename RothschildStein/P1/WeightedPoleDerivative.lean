-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedTaylorParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.P1

variable {N : ℕ}

/-- On the unit gauge ball, a power dominating all coordinate weights
is bounded by the Euclidean coordinate sup norm. -/
theorem kgauge_pow_le_norm (G : HomogeneousGroup N) (W : ℕ)
    (hW : ∀ j, G.weight j ≤ W) (u : Fin N → ℝ) (hu : kgauge G u ≤ 1) :
    kgauge G u ^ W ≤ ‖u‖ := by
  let roots : Set ℝ := Set.range (fun j : Fin N => Real.rpow |u j| ((G.weight j : ℝ)⁻¹))
  have hne : roots.Nonempty := ⟨_, ⟨⟨0, G.dimension_pos⟩, rfl⟩⟩
  obtain ⟨j, hj⟩ := hne.csSup_mem (Set.finite_range _)
  have he : kgauge G u = Real.rpow |u j| ((G.weight j : ℝ)⁻¹) := hj.symm
  calc
    kgauge G u ^ W ≤ kgauge G u ^ G.weight j :=
      pow_le_pow_of_le_one (kgauge_nonneg G u) hu (hW j)
    _ = |u j| := by
      rw [he]
      exact Real.rpow_inv_natCast_pow (abs_nonneg _) (G.weight_pos j).ne'
    _ ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u j

/-- Sufficient weighted decay makes a zero extension differentiable
at the parameter axis, with zero full joint derivative. -/
theorem hasFDerivAt_zero_of_weighted_decay {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : HomogeneousGroup N) (W q : ℕ) (hW : ∀ j, G.weight j ≤ W) (hq : 0 < q)
    (H : P × (Fin N → ℝ) → ℝ) (K : Set P) (p : P) (hK : K ∈ 𝓝 p)
    (hzero : ∀ a ∈ K, H (a, 0) = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a ∈ K, ∀ u : Fin N → ℝ, kgauge G u ≤ 1 →
      |H (a, u)| ≤ C * kgauge G u ^ (W + q)) :
    HasFDerivAt H (0 : (P × (Fin N → ℝ)) →L[ℝ] ℝ) (p, 0) := by
  have hp : p ∈ K := mem_of_mem_nhds hK
  have hρ : Tendsto (fun z : P × (Fin N → ℝ) => kgauge G z.2)
      (𝓝 (p, 0)) (𝓝 0) := by
    simpa only [kgauge, Function.comp_def, (kgauge_eq_zero_iff G 0).mpr rfl] using
      ((G2.continuous_gauge G).tendsto (0 : Fin N → ℝ)).comp
        ((continuous_snd : Continuous (fun z : P × (Fin N → ℝ) => z.2)).tendsto (p, 0))
  have hsmall : ∀ᶠ z : P × (Fin N → ℝ) in 𝓝 (p, 0), kgauge G z.2 ≤ 1 :=
    hρ.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hparam : ∀ᶠ z : P × (Fin N → ℝ) in 𝓝 (p, 0), z.1 ∈ K :=
    continuous_fst.continuousAt.tendsto.eventually hK
  have hmajor : Tendsto (fun z : P × (Fin N → ℝ) => C * kgauge G z.2 ^ q)
      (𝓝 (p, 0)) (𝓝 0) := by
    simpa only [zero_pow hq.ne', mul_zero] using tendsto_const_nhds.mul (hρ.pow q)
  rw [hasFDerivAt_iff_tendsto]
  simp only [hzero p hp, sub_zero, zero_apply, Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun z =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (abs_nonneg _)) ?_ hmajor
  filter_upwards [hparam, hsmall] with z hz hsmall
  by_cases hu : z.2 = 0
  · have he : z = (z.1, 0) := by ext <;> simp [hu]
    rw [he, hzero z.1 hz, abs_zero, mul_zero]
    exact mul_nonneg hC (pow_nonneg (kgauge_nonneg G _) _)
  · have hn : 0 < ‖z - (p, 0)‖ := by
      apply norm_pos_iff.mpr
      intro he
      apply hu
      have hs := congrArg Prod.snd he
      simpa only [Prod.snd_sub, sub_zero, Prod.snd_zero] using hs
    have hρn : kgauge G z.2 ^ W ≤ ‖z - (p, 0)‖ :=
      (kgauge_pow_le_norm G W hW z.2 hsmall).trans (by
        have he : (z - (p, (0 : Fin N → ℝ))).2 = z.2 := by
          ext j
          simp
        rw [← he]
        exact norm_snd_le (z - (p, 0)))
    have hb : |H z| ≤ (C * kgauge G z.2 ^ q) * ‖z - (p, 0)‖ := by
      calc
        |H z| ≤ C * kgauge G z.2 ^ (W + q) := hbound z.1 hz z.2 hsmall
        _ = (C * kgauge G z.2 ^ q) * kgauge G z.2 ^ W := by rw [pow_add]; ring
        _ ≤ (C * kgauge G z.2 ^ q) * ‖z - (p, 0)‖ :=
          mul_le_mul_of_nonneg_left hρn (mul_nonneg hC (pow_nonneg (kgauge_nonneg G _) _))
    calc
      ‖z - (p, 0)‖⁻¹ * |H z| ≤
          ‖z - (p, 0)‖⁻¹ * ((C * kgauge G z.2 ^ q) * ‖z - (p, 0)‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hn.le)
      _ = C * kgauge G z.2 ^ q := by field_simp

end RothschildStein.P1
