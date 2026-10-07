-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CompactParameterContinuity
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology NNReal

namespace RothschildStein.G1

/-- Scale initial and field errors by the same factor in Grönwall's
explicit bound. -/
theorem gronwallBound_diagonal_scale (δ K t : ℝ) :
    gronwallBound δ K δ t = δ * gronwallBound 1 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

/-- Actual flow families vary continuously with locally
compact uniform-space parameters. Joint coefficient continuity on a common
compact spatial carrier and a uniform spatial Lipschitz bound suffice;
there is no parameter derivative hypothesis (BB Props 9.53–9.54, p. 452). -/
theorem flow_solutions_parameter_continuousOn {P E : Type*}
    [UniformSpace P] [LocallyCompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} (hU : IsOpen U) {K : Set E} (hK : IsCompact K)
    (Z : P × E → E) (hZ : ContinuousOn Z (U ×ˢ K))
    (Φ : P → ℝ → E) {T : ℝ} {L : ℝ≥0}
    (hLip : ∀ p ∈ U, LipschitzOnWith L (fun y => Z (p, y)) K)
    (hrange : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) T, Φ p t ∈ K)
    (hode : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (Φ p) (Z (p, Φ p t)) t)
    (hinit : ContinuousOn (fun p => Φ p 0) U) :
    ∀ τ ∈ Icc (0 : ℝ) T, ContinuousOn (fun p => Φ p τ) U := by
  intro τ hτ p₀ hp₀
  change Tendsto (fun p => Φ p τ) (𝓝[U] p₀) (𝓝 (Φ p₀ τ))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := |gronwallBound 1 L 1 τ| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hclose := fields_uniformly_close_on_compact hU hK hZ hp₀ hδ
  have hinitclose : ∀ᶠ p in 𝓝[U] p₀, dist (Φ p 0) (Φ p₀ 0) < δ :=
    (Metric.tendsto_nhds.mp (hinit p₀ hp₀)) δ hδ
  filter_upwards [hclose.filter_mono nhdsWithin_le_nhds, hinitclose,
    self_mem_nhdsWithin] with p hnear hstart hp
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hτ.2
  have hder (q : P) (hq : q ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) :=
    hode q hq t (hsub ht)
  have hbound := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ y => Z (p, y)) (s := fun _ => K) (K := L)
    (εf := 0) (εg := δ) (δ := δ)
    (fun _ _ => hLip p hp)
    (HasDerivAt.continuousOn (hder p hp))
    (fun t ht => (hder p hp t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun _ _ => by simp)
    (fun t ht => hrange p hp t (hsub (Ico_subset_Icc_self ht)))
    (HasDerivAt.continuousOn (hder p₀ hp₀))
    (fun t ht => (hder p₀ hp₀ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => by
      rw [dist_eq_norm, norm_sub_rev]
      exact (hnear _ (hrange p₀ hp₀ t (hsub (Ico_subset_Icc_self ht)))).le)
    (fun t ht => hrange p₀ hp₀ t (hsub (Ico_subset_Icc_self ht))) hstart.le τ ⟨hτ.1, le_rfl⟩
  rw [zero_add, sub_zero, gronwallBound_diagonal_scale] at hbound
  have hgc : gronwallBound 1 L 1 τ ≤ C :=
    (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)
  apply lt_of_le_of_lt (hbound.trans (mul_le_mul_of_nonneg_left hgc hδ.le))
  have heq : δ * C = ε / 2 := by
    dsimp [δ]
    field_simp
  rw [heq]
  linarith

end RothschildStein.G1
