-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartData
public import RothschildStein.L1.CanonicalInverseDomain
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1

/-- Smooth actual frame fields construct all common canonical
chart data, including actual trajectories and both inverse identities. -/
theorem nonempty_canonicalFrameChartData {N : ℕ}
    (Ω : Set (Fin N → ℝ)) (hΩ : IsOpen Ω)
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (x : Fin N → ℝ) (hx : x ∈ Ω)
    (hframe : LinearIndependent ℝ (fun i => Y i x)) :
    Nonempty (CanonicalFrameChartData Ω Y x) := by
  obtain ⟨r₀,hr₀,τ,hτ,Φ,hball,hΦ,hsol,hfix⟩ :=
    exists_smooth_frame_parameter_flow Ω hΩ Y hY x hx
  let a : ℝ := τ/2
  have ha : 0 < a := by dsimp [a]; linarith
  have haτ : a < τ := by dsimp [a]; linarith
  have hat : a ∈ Ioo (-τ) τ := ⟨by linarith,haτ⟩
  have hp : ((0 : Fin N → ℝ),x) ∈ ball (0,x) r₀ := mem_ball_self hr₀
  have hxb : x ∈ ball x r₀ := mem_ball_self hr₀
  obtain ⟨W,hW,hpW,Θ,hΘ,hΘx,hright,hinput,hleft⟩ := canonicalFrameMap_open_inverse_with_domain_of_flow
    hΩ isOpen_ball hτ (ne_of_gt ha) hat Y hY Φ hΦ
    (fun q hq => (hsol q hq).1) (fun q hq t ht => (hsol q hq).2 t ht)
    x hp (fun t ht => hfix x hxb t ht) hframe
  have hODE : ∀ q ∈ ball (0,x) r₀, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧ Φ (q,t) ∈ Ω :=
    fun q hq => ⟨(hsol q hq).1,fun t ht =>
      ⟨((hsol q hq).2 t ht).2,((hsol q hq).2 t ht).1⟩⟩
  have hrev := canonicalFrameMap_reverse_eventually hΩ isOpen_ball hτ hat Y hY Φ hΦ
    hODE x hp (hfix x hxb a hat)
  have hcΘ := (hΘ.contDiffAt (hW.mem_nhds hpW)).continuousAt
  have hanti := canonicalInverse_antisymmetric_eventually (canonicalFrameMap a Φ) Θ x
    hcΘ hΘx (Filter.mem_of_superset (hW.mem_nhds hpW) hright) hleft hrev
  obtain ⟨V,hVsub,hVopen,hpV⟩ := _root_.mem_nhds_iff.mp hanti
  let W' := W ∩ V
  have hW' : IsOpen W' := hW.inter hVopen
  have hpW' : (x,x) ∈ W' := ⟨hpW,hpV⟩
  have hKx : canonicalFrameMap a Φ (x,0) = x := by
    simpa [canonicalFrameMap] using hfix x hxb a hat
  have hpO : (x,0) ∈ canonicalFrameDomain a (ball (0,x) r₀) := by
    simpa [canonicalFrameDomain] using hp
  obtain ⟨c,hc,hKc,hcsub⟩ := exists_common_coefficient_patch (canonicalFrameMap a Φ) Θ x
    (canonicalFrameDomain_isOpen a isOpen_ball) hpO (canonicalFrameMap_contDiffOn a hat Φ hΦ)
    hKx hW' hpW' hleft
  obtain ⟨b,hb,hbsub,_⟩ := exists_symmetric_product_patch hW' x hpW'
  have hframes := frame_linearIndependent_eventually Y x
    (fun i => ((hY i).contDiffAt (hΩ.mem_nhds hx)).continuousAt) hframe
  obtain ⟨f,hf,hfsub⟩ := Metric.mem_nhds_iff.mp hframes
  let R := min c (min b (min r₀ f))
  have hR : 0 < R := lt_min hc (lt_min hb (lt_min hr₀ hf))
  let r := R/2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hrc : r ≤ c := le_trans (le_of_lt hrR) (min_le_left _ _)
  have hrb : r ≤ b := le_trans (le_trans (le_of_lt hrR) (min_le_right _ _)) (min_le_left _ _)
  have hRm : R ≤ min r₀ f := le_trans (min_le_right _ _) (min_le_right _ _)
  have hrr₀lt : r < r₀ := lt_of_lt_of_le hrR (le_trans hRm (min_le_left _ _))
  have hrr₀ : r ≤ r₀ := le_of_lt hrr₀lt
  have hrf : r ≤ f := le_trans (le_trans (le_of_lt hrR) hRm) (min_le_right _ _)
  have hclosed : closedBall x r ⊆ Ω := by
    intro y hy
    have hp₀ : ((0 : Fin N → ℝ),y) ∈ ball (0,x) r₀ := by
      rw [mem_ball,Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist y x)]
      exact lt_of_le_of_lt hy hrr₀lt
    have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
    have hh := ((hODE (0,y) hp₀).2 0 hzero).2
    rwa [(hODE (0,y) hp₀).1] at hh
  have hsubc : ball x r ×ˢ ball (0 : Fin N → ℝ) r ⊆ ball x c ×ˢ ball 0 c :=
    fun q hq => ⟨ball_subset_ball hrc hq.1,ball_subset_ball hrc hq.2⟩
  refine ⟨{
    initialRadius := r₀, initialRadius_pos := hr₀,
    timeRadius := τ, timeRadius_pos := hτ, time := a, time_pos := ha, time_lt := haτ,
    flow := Φ, flow_smooth := hΦ, flow_ode := hODE, flow_zero := hfix,
    inverseDomain := W', inverseDomain_open := hW', theta := Θ,
    theta_smooth := hΘ.mono inter_subset_left,
    right_inverse := fun q hq => hright q hq.1,
    inverse_parameters := fun q hq => hinput q hq.1,
    radius := r, radius_pos := hr, radius_le_initial := hrr₀, closedPatch_subset := hclosed,
    basePatch_subset := fun q hq => hbsub
      ⟨ball_subset_ball hrb hq.1,ball_subset_ball hrb hq.2⟩,
    antisymmetric := fun q hq => hVsub hq.2,
    frame := fun y hy => hfsub (ball_subset_ball hrf hy),
    forward_smooth := hKc.mono hsubc,
    coefficients := fun q hq => hcsub q (hsubc hq) }⟩
end RothschildStein.L1
