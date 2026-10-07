-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesHomogeneous
public import RothschildStein.G2.PowerBochner

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ}

/-- A proved uniform subcritical model bound
implies an actual O(ε) small-ball integral for the prescribed gauge.
The coordinate gauge is used only for an integrable majorant. -/
theorem uniformModel_smallBall_bound (G : HomogeneousGroup N)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {K : Set (Fin N → ℝ)} (f : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hb : ∀ ξ ∈ K, ∀ u, u ≠ 0 → kgauge G u ≤ δ →
      ‖f ξ u‖ ≤ M * kgauge G u ^ (1 - (G.homogeneousDimension : ℝ))) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖∫ u in {u | ν u ≤ ε}, f ξ u‖ ≤ A * ε := by
  let rsUniformSmallBallFinNonempty : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  obtain ⟨a, b, ha, _, hg⟩ := G2.gauge_equivalent_max hν
  let Q : ℝ := G.homogeneousDimension
  let V : ℝ := (volume {u | kgauge G u < 1}).toReal
  refine ⟨a * δ, M * (Q * V) / a, mul_pos ha hδ,
    div_nonneg (mul_nonneg hM (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)) ha.le, ?_⟩
  intro ξ hξ ε hε hεr
  have hset : {u | ν u ≤ ε} ⊆ {u | kgauge G u ≤ ε / a} := by
    intro u hu
    change kgauge G u ≤ ε / a
    rw [le_div_iff₀ ha]
    simpa only [mul_comm] using (hg u).1.trans hu
  have hrδ : ε / a ≤ δ := (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hεr)
  have hi : IntegrableOn (fun u => kgauge G u ^ (1 - Q)) {u | kgauge G u ≤ ε / a} volume := by
    have hp := (G2.integrableOn_power_near_iff (G2.isHomogeneousGauge_max G)
      (Q - 1) (div_pos hε ha)).mpr (by dsimp only [Q]; linarith)
    have he : -(Q - 1) = 1 - Q := by ring
    rw [he] at hp
    exact hp
  have hiM : IntegrableOn (fun u => M * kgauge G u ^ (1 - Q))
      {u | kgauge G u ≤ ε / a} volume := hi.const_mul M
  have hn : ‖∫ u in {u | ν u ≤ ε}, f ξ u‖ ≤
      ∫ u in {u | ν u ≤ ε}, M * kgauge G u ^ (1 - Q) := by
    apply norm_integral_le_of_norm_le (hiM.mono_set hset)
    filter_upwards [ae_restrict_mem (isClosed_le hν.1 continuous_const).measurableSet,
      ae_restrict_of_ae (volume.ae_ne (0 : Fin N → ℝ))] with u hu h0
    exact hb ξ hξ u h0 ((hset hu).trans hrδ)
  have hmono : (∫ u in {u | ν u ≤ ε}, M * kgauge G u ^ (1 - Q)) ≤
      ∫ u in {u | kgauge G u ≤ ε / a}, M * kgauge G u ^ (1 - Q) := by
    apply setIntegral_mono_set hiM
    · exact Eventually.of_forall (fun u => mul_nonneg hM (Real.rpow_nonneg (kgauge_nonneg G u) _))
    · exact Eventually.of_forall (fun u hu => hset hu)
  have he : (∫ u in {u | kgauge G u ≤ ε / a}, kgauge G u ^ (1 - Q)) = Q * V * (ε / a) := by
    have hp := G2.integral_power_near (G2.isHomogeneousGauge_max G)
      (β := Q - 1) (by dsimp only [Q]; linarith) (div_pos hε ha)
    have hneg : -(Q - 1) = 1 - Q := by ring
    have hdiff : (G.homogeneousDimension : ℝ) - (Q - 1) = 1 := by dsimp only [Q]; ring
    simpa only [hneg, hdiff, Real.rpow_one, div_one, Q, V] using hp
  calc
    _ ≤ ∫ u in {u | ν u ≤ ε}, M * kgauge G u ^ (1 - Q) := hn
    _ ≤ ∫ u in {u | kgauge G u ≤ ε / a}, M * kgauge G u ^ (1 - Q) := hmono
    _ = M * (Q * V * (ε / a)) := by rw [integral_const_mul, he]
    _ = (M * (Q * V) / a) * ε := by ring

end RothschildStein.P1
