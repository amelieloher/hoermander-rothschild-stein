-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoDyadic
public import RothschildStein.H2.CampanatoRadii
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Limits of nested dyadic radius sequences coincide.
BB Lemma 7.42, p. 329; every center lies in S. -/
theorem campanato_dyadic_limit_unique (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hsρ : s ≤ 6 * P.ρ)
    {Lr Ls : ℝ}
    (hLr : Tendsto (fun n => campanatoConstant P u x (campanatoRadius r n)) atTop (𝓝 Lr))
    (hLs : Tendsto (fun n => campanatoConstant P u x (campanatoRadius s n)) atTop (𝓝 Ls)) :
    Lr = Ls := by
  let q := (1 / 2 : ℝ) ^ α
  let C := (campanatoSeminorm α P u).toReal *
    (r ^ α + s ^ α * (P.C_D * (s / r) ^ Real.logb 2 P.C_D))
  have hs : 0 < s := hr.trans_le hrs
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hb (n : ℕ) :
      |campanatoConstant P u x (campanatoRadius r n) -
        campanatoConstant P u x (campanatoRadius s n)| ≤ C * q ^ n := by
    have hfr := campanatoRadius_facts hr n
    have hfs := campanatoRadius_facts hs n
    have hsub : campanatoRadius r n ≤ campanatoRadius s n :=
      mul_le_mul_of_nonneg_right hrs (by positivity)
    have he : campanatoRadius s n / campanatoRadius r n = s / r := by
      dsimp [campanatoRadius]; field_simp
    have hh := campanatoConstant_radii P hu hx hfr.1 hsub (hfs.2.1.trans hsρ)
    rw [he, campanatoRadius_rpow hr n, campanatoRadius_rpow hs n] at hh
    dsimp [C, q]; nlinarith
  have hz : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
  have hh : |Lr - Ls| ≤ 0 := le_of_tendsto_of_tendsto (hLr.sub hLs).abs hz
    (Eventually.of_forall hb)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

/-- The canonical Campanato representative uses the maximal controlled
radius 6ρ. Off S its value is fixed to zero. -/
def campanatoRepresentative (P : DoublingPatch X) (α : ℝ) (u : X → ℝ) : X → ℝ := by
  classical
  exact fun x => if h : 0 < α ∧ MemCampanato α P u ∧ x ∈ P.S then
    (campanato_dyadic_limit P h.1 h.2.1 h.2.2
      (show 0 < 6 * P.ρ by linarith [P.ρ_pos]) le_rfl).choose else 0

/-- All controlled dyadic sequences converge to the same representative. -/
theorem campanatoRepresentative_tendsto (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    Tendsto (fun n => campanatoConstant P u x (campanatoRadius r n))
      atTop (𝓝 (campanatoRepresentative P α u x)) := by
  classical
  obtain ⟨L, hL, _⟩ := campanato_dyadic_limit P hα hu hx hr hrρ
  have hc := (campanato_dyadic_limit P hα hu hx
    (show 0 < 6 * P.ρ by linarith [P.ρ_pos]) le_rfl).choose_spec.1
  have he := campanato_dyadic_limit_unique P hα hu hx hr hrρ le_rfl hL hc
  rw [he] at hL
  simpa [campanatoRepresentative, hα, hu, hx] using hL

/-- Distance from every minimiser to the canonical representative,
with c_C = (C_D+1)/(1-2^{-α}) (BB (7.31), Lemma 7.42). -/
theorem campanatoRepresentative_approx (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    |campanatoConstant P u x r - campanatoRepresentative P α u x| ≤
      ((P.C_D + 1) / (1 - (1 / 2 : ℝ) ^ α)) * r ^ α * (campanatoSeminorm α P u).toReal := by
  obtain ⟨L, hL, hb⟩ := campanato_dyadic_limit P hα hu hx hr hrρ
  have he := tendsto_nhds_unique hL (campanatoRepresentative_tendsto P hα hu hx hr hrρ)
  rw [he] at hb
  have hh := hb 0
  simp only [campanatoRadius, pow_zero, mul_one] at hh
  convert hh using 1; ring
end RothschildStein.H2
