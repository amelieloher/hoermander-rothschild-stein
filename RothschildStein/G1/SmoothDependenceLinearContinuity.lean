-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceLinearComparison
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology NNReal

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P]
  [LocallyCompactSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Jointly continuous coefficients converge uniformly in time
as the parameter approaches a fixed point (BB Proposition 1.2, p. 3). -/
theorem linear_coefficients_uniformly_close
    {U : Set P} (hU : IsOpen U) {A : (P × ℝ) → E →L[ℝ] E} {T : ℝ}
    (hA : ContinuousOn A (U ×ˢ Icc (-T) T)) {x : P} (hx : x ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (-T) T, ‖A (y, t) - A (x, t)‖ < ε := by
  have hpull : ContinuousOn
      (fun p : P × Icc (-T) T => A (p.1, p.2)) (U ×ˢ univ) := by
    apply hA.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1, p.2.property⟩
  have hu := ContinuousOn.tendstoUniformly
    (f := fun x (t : Icc (-T) T) => A (x, t)) (hU.mem_nhds hx) hpull
  have he := (Metric.tendstoUniformly_iff.mp hu) ε hε
  filter_upwards [he] with y hy
  intro t ht
  simpa only [dist_eq_norm, norm_sub_rev] using hy ⟨t, ht⟩

/-- Initial-parameter continuity of a bounded family of
linear solutions follows from coefficient continuity and Grönwall. No
parameter derivative or continuity of the solution family is assumed
(BB Proposition 1.2, p. 3). -/
theorem linear_solutions_parameter_continuousOn
    {U : Set P} (hU : IsOpen U) {A : (P × ℝ) → E →L[ℝ] E}
    {W : P → ℝ → E} {T K R : ℝ} (hT : 0 < T) (hR : 0 ≤ R)
    (hA : ContinuousOn A (U ×ˢ Icc (-T) T))
    (hAb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖A (x, t)‖ ≤ K)
    (hW : ∀ x ∈ U, ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt (W x) (A (x, t) (W x t)) (Icc (-T) T) t)
    (hWb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖W x t‖ ≤ R)
    (hinit : ∀ x ∈ U, ∀ y ∈ U, W x 0 = W y 0)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) : ContinuousOn (fun x => W x t) U := by
  intro x hx
  change Tendsto (fun y => W y t) (𝓝[U] x) (𝓝 (W x t))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C := |gronwallBound 0 K 1 (|t|)| * R + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he := linear_coefficients_uniformly_close hU hA hx hδ
  have he' : ∀ᶠ y in 𝓝[U] x, ∀ v ∈ Icc (-T) T, ‖A (y, v) - A (x, v)‖ < δ :=
    he.filter_mono nhdsWithin_le_nhds
  filter_upwards [he', self_mem_nhdsWithin] with y hy hyU
  have hs : uIcc 0 t ⊆ Ioo (-T) T :=
    ordConnected_Ioo.uIcc_subset (show (0 : ℝ) ∈ Ioo (-T) T from ⟨by linarith, hT⟩) ht
  have hd (z : P) (hz : z ∈ U) (v : ℝ) (hv : v ∈ uIcc 0 t) :
      HasDerivAt (W z) (A (z, v) (W z v)) v :=
    (hW z hz v (Ioo_subset_Icc_self (hs hv))).hasDerivAt
      (Icc_mem_nhds (hs hv).1 (hs hv).2)
  have hb := linear_curve_comparison_bound hδ.le (hd y hyU) (hd x hx)
    (hinit y hyU x hx)
    (fun v hv => hAb y hyU v (Ioo_subset_Icc_self (hs hv)))
    (fun v hv => (hy v (Ioo_subset_Icc_self (hs hv))).le)
    (fun v hv => hWb x hx v (Ioo_subset_Icc_self (hs hv)))
  rw [gronwallBound_zero_scale] at hb
  have hgc : gronwallBound 0 K 1 |t| * R ≤ C := by
    dsimp [C]
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) hR).trans
      (le_add_of_nonneg_right zero_le_one)
  have hb' : ‖W y t - W x t‖ ≤ δ * C := by
    exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgc hδ.le)
  rw [dist_eq_norm]
  apply lt_of_le_of_lt hb'
  have heq : δ * C = ε / 2 := by
    dsimp [δ]
    field_simp
  rw [heq]
  linarith

end RothschildStein.G1
