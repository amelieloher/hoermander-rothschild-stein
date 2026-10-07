-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ParameterShiftedChartWithJacobian
public import RothschildStein.G4.ShiftedBallBoxFromChart
public import RothschildStein.G4.ChartDataRestriction
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.G4

/-- Actual shifted ball-box charts uniformly over a compact
external parameter carrier and compact center set. Spatial jets are
jointly continuous; the external parameter is never differentiated.
All conclusions concern the same constructed flow family. -/
theorem exists_parameter_shifted_ball_box {Sg : Type*}
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
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKball : K ⊆ ball x₀ (R/8))
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Sg → Fin m → (Fin n → ℝ) → (Fin n → ℝ) :=
      fun σ j => shortField w (X σ) (shortIndex w j)
    ∃ a b r₀ D κ : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ D ∧ 0 < κ ∧ (n : ℝ)*κ ≤ 1/4 ∧
      ∃ Φ : Sg → (Fin n → Fin m) →
        (((Fin (n+m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B, IsSuboptimal (Zf σ) wf B x t r → ∀ v ∈ weightedBox wf (b*r),
      let F := fun u => Φ σ B ((Fin.append u v,x),1)
      let Q := weightedBox (wf ∘ B) (a*r)
      ChartAnalyticBounds Ω wf (Zf σ) B F Q r κ D ∧
      ChartTrajectories Ω (Zf σ) B F Q x v (fun u τ => Φ σ B ((Fin.append u v,x),τ)) ∧
      (v = 0 → F 0 = x) ∧ InjOn F Q ∧
      (∀ u ∈ Q, |frameDet (Zf σ) B x|/4 ≤ |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4*|frameDet (Zf σ) B x|) ∧
      ({y | auxiliaryDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal (b*r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | constantShortDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal (2*a*r)}) ∧
      ({y | constantShortDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal (2*a*r)} ⊆
        {y | auxiliaryDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal (2*a*r)}) ∧
      (v = 0 → F '' Q ⊆
        {y | constantShortDistance (s := s) Ω w (X σ) x y < ENNReal.ofReal (a*r)}) ∧
      IsOpen (F '' Q) ∧ ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Ψ (F '' Q) ∧
        (∀ y ∈ F '' Q, Ψ y ∈ Q ∧ F (Ψ y) = y) ∧ (∀ u ∈ Q, Ψ (F u) = u) ∧
        ∀ y ∈ F '' Q, ∀ ℓ i : Fin n,
          |(fderiv ℝ Ψ y (Zf σ (B ℓ) y)) i| ≤ (4/3 : ℝ)*
            r ^ (((wf (B i) : ℕ) : ℤ) - ((wf (B ℓ) : ℕ) : ℤ)) := by
  intro m wf Zf
  obtain ⟨Φ,D,κ,r₀,c,hD,hκ,hsmall,hr₀,hr₀1,hc,hc1,_hflow,hcharts⟩ :=
    exists_parameter_shifted_chart_with_jacobian k n s h q hn hs horder hq w M Δ R
      hM hΔ hR Ω hΩ X hX hstep hjoint x₀ hRΩ hjets hmax K hK hKball t ht ht1
  let a := c/2
  have ha : 0 < a := half_pos hc
  have hac : a ≤ c := (half_le_self hc.le)
  have ha1 : a < 1 := by dsimp [a]; linarith
  obtain ⟨b,hb,hba,hb1,hball⟩ := exists_shifted_ball_box_radius (m := m) (n := n) (s := s) ha ha1.le hD.le
  refine ⟨a,b,r₀,D,κ,ha,ha1,hb,hba,hb1,hr₀,hr₀1,hD.le,hκ,hsmall,Φ,?_⟩
  intro σ x hx r hr hrr B hB v hv F Q
  have hbc : b ≤ c := by linarith
  have hvC := weightedBox_subset_of_radius_le wf (mul_nonneg hb.le hr.le)
    (mul_le_mul_of_nonneg_right hbc hr.le) hv
  obtain ⟨hinj,hAB,htraj,hzero,hjac⟩ := hcharts σ x hx r hr hrr B hB v hvC
  have hQC : Q ⊆ weightedBox (wf ∘ B) (c*r) :=
    weightedBox_subset_of_radius_le (wf ∘ B) (mul_nonneg ha.le hr.le) (mul_le_mul_of_nonneg_right hac hr.le)
  have hAB' := chartAnalyticBounds_mono hAB hQC
  have htraj' := chartTrajectories_mono htraj hQC
  have hinj' := hinj.mono hQC
  have hw : ∀ i, (wf (B i) : ℕ) ≤ s := fun i =>
    ((mem_shortWordFamily_iff w (shortIndex w (B i)).val).mp (shortIndex w (B i)).property).2
  have hxR : x ∈ closedBall x₀ R := ball_subset_closedBall
    (ball_subset_ball (by linarith) (hKball hx))
  have hspan : ∃ C : Fin n → Fin m, frameDet (Zf σ) C x ≠ 0 := by
    obtain ⟨C,hC⟩ := hmax σ x hxR
    refine ⟨(Fintype.equivFin (ShortWord w s)) ∘ C,?_⟩
    have hne := abs_pos.mp (hΔ.trans_le hC)
    simpa only [Zf,shortIndex,frameDet_reindex] using hne
  have hBx := suboptimal_frame_ne_zero ht hr hspan hB
  have hresult := hball wf (Zf σ) B hw Ω x F
    (fun u τ => Φ σ B ((Fin.append u v,x),τ)) r κ hr (hrr.trans hr₀1)
    hκ.le hsmall v hv hBx hAB' htraj' hinj'
  refine ⟨hAB',htraj',hzero,hinj',fun u hu => hjac u (hQC hu),?_⟩
  exact hresult
end RothschildStein.G4
