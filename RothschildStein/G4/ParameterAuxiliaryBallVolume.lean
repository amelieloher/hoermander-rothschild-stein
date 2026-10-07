-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ParameterShiftedBallBox
public import RothschildStein.G4.ControlTopology
public import RothschildStein.G4.UniformVolumeConstantsFromCharts
public import RothschildStein.G4.FrameVolumeAdapters
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4
open G1

/-- Actual auxiliary volumes share constants over the entire
compact parameter family on one spatial buffer (BB pp. 405–406). -/
theorem exists_parameter_auxiliary_ball_volume_bounds {Sg : Type*}
    [UniformSpace Sg] [CompactSpace Sg] (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Sg → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ j, ContDiffOn ℝ (⊤ : ℕ∞) (X σ j) Ω)
    (hstep : ∀ σ, bracketStepOn Ω w (X σ) s)
    (hjoint : ∀ J, ∀ i ≤ s+1, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2) (univ ×ˢ Ω))
    (x₀ : Fin n → ℝ) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ σ j, HasJetBound Ω (closedBall x₀ R) (X σ j)
      (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s))) M)
    (hmax : ∀ σ, ∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
      Δ ≤ |frameDet (shortField w (X σ)) B y|)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKball : K ⊆ ball x₀ (R/8)) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf := fun σ j => shortField w (X σ) (shortIndex (s := s) w j)
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ ε →
        let Λ := volumePolynomial (fun B : Fin n → Fin m => frameDet (Zf σ) B x)
          (fun B => ∑ i, (wf (B i) : ℕ)) r
        ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω wf (Zf σ) x r) ∧
        volume (controlBall Ω wf (Zf σ) x r) ≤ ENNReal.ofReal (C*Λ) := by
  classical
  intro m wf Zf
  obtain ⟨a,b,r₀,D,κ,ha,ha1,hb,_hba,hb1,hr₀,_hr1,_hD,_hκ,_hnκ,Φ,hcharts⟩ :=
    exists_parameter_shifted_ball_box k n s h q hn hs horder hq w M Δ R hM hΔ hR
      Ω hΩ X hX hstep hjoint x₀ hRΩ hjets hmax K hK hKball
      (1/2) (by norm_num) (by norm_num)
  have hw : ∀ B : Fin n → Fin m, (∑ i, (wf (B i) : ℕ)) ≤ n*s := by
    intro B
    exact frame_natural_weight_le wf
      (fun j => ((mem_shortWordFamily_iff w (shortIndex w j).val).mp (shortIndex w j).property).2) B
  obtain ⟨c,C,ε,hc,hC,hε,hvol⟩ :=
    exists_uniform_volume_constants_of_actual_weighted_charts
      (fun B : Fin n → Fin m => wf ∘ B) (n*s) hw ha ha1.le hb (by linarith) hr₀
  refine ⟨c,C,ε,hc,hC,hε,?_⟩
  intro σ x hx
  apply hvol (fun B => frameDet (Zf σ) B x) (fun r => controlBall Ω wf (Zf σ) x r)
  intro r hr hrr
  have hxR : x ∈ closedBall x₀ R := ball_subset_closedBall
    (ball_subset_ball (by linarith) (hKball hx))
  have hspan : ∃ B : Fin n → Fin m, frameDet (Zf σ) B x ≠ 0 := by
    obtain ⟨B,hB⟩ := hmax σ x hxR
    refine ⟨(Fintype.equivFin (ShortWord w s)) ∘ B,?_⟩
    have hnz := abs_pos.mp (hΔ.trans_le hB)
    simpa only [Zf,shortIndex,frameDet_reindex] using hnz
  obtain ⟨B,hB⟩ := exists_suboptimal_frame (Zf σ) wf (t := 1) le_rfl hr hspan
  have hbest : ∀ A, |frameDet (Zf σ) A x| *r^(∑ i, (wf (A i) : ℕ)) ≤
      |frameDet (Zf σ) B x| *r^(∑ i, (wf (B i) : ℕ)) := by
    intro A
    simpa only [IsSuboptimal,frameWeight_eq_nat_sum,zpow_natCast,one_mul] using hB A
  have hhalf : IsSuboptimal (Zf σ) wf B x (1/2) r := by
    intro A
    exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (zpow_nonneg hr.le _))
      (by norm_num : (1/2 : ℝ) ≤ 1)).trans (by simpa only [one_mul] using hB A)
  have hzero : (0 : Fin m → ℝ) ∈ weightedBox wf (b*r) := by
    intro j
    simpa only [Pi.zero_apply,abs_zero] using pow_pos (mul_pos hb hr) (wf j : ℕ)
  obtain ⟨hAB,_htraj,_hinit,hinj,hjac,hinner,_hout,_haux,houter,_htail⟩ :=
    hcharts σ x hx r hr hrr B hhalf 0 hzero
  refine ⟨B,hbest,_,hAB.1,hinj,hjac,hinner,?_⟩
  intro y hy
  have hh := houter rfl hy
  exact lt_of_le_of_lt (auxiliaryDistance_le_constantShortDistance Ω w (X σ) x y)
    (hh.trans_le (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left hr.le ha1.le)))
end RothschildStein.G4
