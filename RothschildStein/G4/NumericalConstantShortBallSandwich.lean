-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.UniformSelectedChartData
public import RothschildStein.G4.ShiftedChartBallRadius
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G4

/-- Uniform primitive finite-jet and rank
budgets give constant-control ball containment. Constants are chosen
before the domain and fields; no injectivity theorem is used. -/
theorem exists_numerical_constant_short_ball_sandwich (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    ∃ A ρ : ℝ, 0 < A ∧ 0 < ρ ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s))) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ x ∈ ball x₀ (R/8), ∀ r : ℝ, 0 < r → r ≤ ρ →
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ⊆
        {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (A*r)} := by
  let m := Fintype.card (ShortWord w s)
  obtain ⟨D₀,hD₀,κ,hκ,hsmall,hprovider⟩ :=
    exists_uniform_selected_chart_data k n s h q hn hs horder hq w M Δ R hM hΔ hR
  obtain ⟨e,he,he1,_het,_heδ,hcharts⟩ := hprovider (1/2) (by norm_num) (by norm_num)
  let D := 2*D₀*(1/2 : ℝ)⁻¹^n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨b,hb,_hba,_hb1,hball⟩ := exists_shifted_chart_ball_radius (m := m) (n := n) (s := s) he he1 hD
  refine ⟨e/b,b,div_pos he hb,hb,?_⟩
  intro Ω hΩ X hX hstep x₀ hRΩ hjets hmax x hx r hr hrr y hy
  let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
  let Zf : Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun j => shortField w X (shortIndex w j)
  have hxΩ : x ∈ Ω := hRΩ (ball_subset_closedBall (ball_subset_ball (by linarith) hx))
  have hrb : 0 < r/b := div_pos hr hb
  have hrb1 : r/b ≤ 1 := (div_le_iff₀ hb).mpr (by simpa using hrr)
  obtain ⟨B,hB⟩ := exists_suboptimal_frame (shortField w X) (shortWeight w)
    (t := 1/2) (by norm_num) hrb (exists_short_frame hstep hxΩ)
  obtain ⟨Φ,_hsmooth,_hflow,hgeometry⟩ := hcharts Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  have hv : (0 : Fin m → ℝ) ∈ weightedBox wf (e*(r/b)) := by
    intro i
    simp only [Pi.zero_apply,abs_zero]
    exact pow_pos (mul_pos he hrb) _
  obtain ⟨hAB,htraj,_hzero⟩ := hgeometry x hx (r/b) hrb hrb1 hB
    e e he le_rfl he le_rfl 0 hv
  let Bf := (Fintype.equivFin (ShortWord w s)) ∘ B
  let F := fun u => Φ ((Fin.append u 0,x),1)
  have hweights : wf ∘ Bf = shortWeight w ∘ B := by
    funext i
    simp [wf,Bf,shortIndex]
  have hw : ∀ i, (wf (Bf i) : ℕ) ≤ s := by
    intro i
    have hh := ((mem_shortWordFamily_iff w (B i).val).mp (B i).property).2
    simpa [wf,Bf,shortIndex,shortWeight,PNat.mk_coe] using hh
  have hBx : frameDet Zf Bf x ≠ 0 := by
    have hh := suboptimal_frame_ne_zero (by norm_num : (0 : ℝ) < 1/2) hrb
      (exists_short_frame hstep hxΩ) hB
    simpa only [Zf,Bf,shortIndex,frameDet_reindex] using hh
  have hvb : (0 : Fin m → ℝ) ∈ weightedBox wf (b*(r/b)) := by
    intro i
    simp only [Pi.zero_apply,abs_zero]
    exact pow_pos (mul_pos hb hrb) _
  have hAB' : ChartAnalyticBounds Ω wf Zf Bf F (weightedBox (wf ∘ Bf) (e*(r/b))) (r/b) κ D := by
    simpa only [hweights] using hAB
  have htraj' : ChartTrajectories Ω Zf Bf F (weightedBox (wf ∘ Bf) (e*(r/b))) x 0
      (fun u τ => Φ ((Fin.append u 0,x),τ)) := by
    simpa only [hweights] using htraj
  have hresult := hball wf Zf Bf hw Ω x F (fun u τ => Φ ((Fin.append u 0,x),τ))
    (r/b) κ hrb hrb1 hκ.le hsmall 0 hvb hBx hAB' htraj'
  have hbr : b*(r/b) = r := by field_simp
  have hy' : controlDistance Ω wf Zf x y < ENNReal.ofReal (b*(r/b)) := by
    simpa only [hbr,auxiliaryDistance,wf,Zf,Set.mem_ofPred_eq] using hy
  have hh := hresult.2.2.2 rfl (hresult.1 hy')
  have her : e*(r/b) = (e/b)*r := by ring
  simpa only [her,constantShortDistance,wf,Zf] using hh
end RothschildStein.G4
