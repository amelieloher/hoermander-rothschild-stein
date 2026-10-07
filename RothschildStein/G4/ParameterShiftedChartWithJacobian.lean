-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CompactParameterSelectedFlowInjectivity
public import RothschildStein.G4.ContinuousShortFieldJets
public import RothschildStein.G4.UniformWordJetBounds
public import RothschildStein.G4.SelectedChartDataWithJacobian
public import RothschildStein.G4.SuboptimalFrameReindex

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Compact parameter families retain actual injectivity,
analytic estimates, trajectories and factor-four Jacobians for the same
shifted flow charts. The external parameter is never differentiated. -/
theorem exists_parameter_shifted_chart_with_jacobian {Sg : Type*}
    [UniformSpace Sg] [CompactSpace Sg] (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) (M Δ R : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Sg → Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ j, ContDiffOn ℝ (⊤ : ℕ∞) (X σ j) Ω)
    (hstep : ∀ σ, bracketStepOn Ω w (X σ) s)
    (hjoint : ∀ J, ∀ i ≤ s + 1, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2) (univ ×ˢ Ω))
    (x₀ : Fin n → ℝ) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ σ j, HasJetBound Ω (closedBall x₀ R) (X σ j)
      (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M)
    (hmax : ∀ σ, ∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
      Δ ≤ |frameDet (shortField w (X σ)) B y|)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKball : K ⊆ ball x₀ (R / 8))
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    let m := Fintype.card (ShortWord w s)
    let δ := R / (64 * (1 + ((n + m : ℕ) : ℝ) * wordJetBase n 0 s M ^ s))
    let wf : Fin m → ℕ+ := fun J => shortWeight w (shortIndex w J)
    let Zf : Sg → Fin m → (Fin n → ℝ) → (Fin n → ℝ) :=
      fun σ J => shortField w (X σ) (shortIndex w J)
    ∃ Φ : Sg → (Fin n → Fin m) →
      (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ∃ D κ r₀ c : ℝ, 0 < D ∧ 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
        0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < c ∧ c ≤ 1 ∧
      (∀ σ B, ContDiffOn ℝ (⊤ : ℕ∞) (Φ σ B)
        ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
        ∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ σ B ((a, x), 0) = x ∧
          ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ σ B ((a, x), τ) ∈ ball x₀ R ∧
            HasDerivAt (fun v => Φ σ B ((a, x), v))
              (∑ j, a j • shortField w (X σ)
                (selectedAuxiliaryIndex w (shortIndex w ∘ B) j) (Φ σ B ((a, x), τ))) τ) ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B, IsSuboptimal (Zf σ) wf B x t r →
      ∀ v ∈ weightedBox wf (c * r),
        let F := fun u => Φ σ B ((Fin.append u v, x), 1)
        let Γ := fun u τ => Φ σ B ((Fin.append u v, x), τ)
        InjOn F (weightedBox (wf ∘ B) (c * r)) ∧
        ChartAnalyticBounds Ω wf (Zf σ) B F (weightedBox (wf ∘ B) (c * r)) r κ D ∧
        ChartTrajectories Ω (Zf σ) B F (weightedBox (wf ∘ B) (c * r)) x v Γ ∧
        (v = 0 → F 0 = x) ∧
        (∀ u ∈ weightedBox (wf ∘ B) (c*r),
          |frameDet (Zf σ) B x|/4 ≤ |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
          |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤ 4*|frameDet (Zf σ) B x|) := by
  classical
  intro m δ wf Zf
  obtain ⟨D₀, hD₀, κ, hκ, hsmall, hprovider⟩ :=
    exists_uniform_selected_chart_data_with_jacobian k n s h q hn hs horder hq w M Δ R hM hΔ hR
  obtain ⟨e, he, he1, _het, heδ, hcharts⟩ := hprovider t ht ht1.le
  have hfamily : ∀ σ, ∀ B : Fin n → Fin m, ∃ Φ :
      (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
      (∀ p ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((p, x), 0) = x ∧
        ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((p, x), τ) ∈ ball x₀ R ∧
          HasDerivAt (fun v => Φ ((p, x), v))
            (∑ j, p j • shortField w (X σ) (selectedAuxiliaryIndex w (shortIndex w ∘ B) j)
              (Φ ((p, x), τ))) τ) ∧
      ∀ x ∈ ball x₀ (R / 8), ∀ r : ℝ, 0 < r → r ≤ 1 →
        IsSuboptimal (Zf σ) wf B x t r →
      ∀ a b : ℝ, 0 < a → a ≤ e → 0 < b → b ≤ e →
      ∀ v ∈ weightedBox wf (b * r),
        ChartAnalyticBounds Ω wf (Zf σ) B (fun u => Φ ((Fin.append u v, x), 1))
          (weightedBox (wf ∘ B) (a * r)) r κ (2 * D₀ * t⁻¹ ^ n) ∧
        ChartTrajectories Ω (Zf σ) B (fun u => Φ ((Fin.append u v, x), 1))
          (weightedBox (wf ∘ B) (a * r)) x v (fun u τ => Φ ((Fin.append u v, x), τ)) ∧
        (v = 0 → Φ ((Fin.append 0 v, x), 1) = x) ∧
        (∀ u ∈ weightedBox (wf ∘ B) (a*r),
          |frameDet (Zf σ) B x|/4 ≤
            |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ (fun u => Φ ((Fin.append u v,x),1)) u))| ∧
          |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ (fun u => Φ ((Fin.append u v,x),1)) u))| ≤
            4*|frameDet (Zf σ) B x|) := by
    intro σ B
    let Bs : Fin n → ShortWord w s := shortIndex w ∘ B
    have hBf : (Fintype.equivFin (ShortWord w s)) ∘ Bs = B := by
      funext i
      simp [Bs, shortIndex]
    have hweights : shortWeight w ∘ Bs = wf ∘ B := rfl
    obtain ⟨Φ, hΦ, hflow, hgeometry⟩ := hcharts Ω hΩ (X σ) (hX σ) (hstep σ) x₀ hRΩ (hjets σ) (hmax σ) Bs
    refine ⟨Φ, hΦ, hflow, ?_⟩
    intro x hx r hr hr1 hB a b ha hae hb hbe v hv
    have hBs : IsSuboptimal (shortField w (X σ)) (shortWeight w) Bs x t r := by
      apply (isSuboptimal_reindex (Fintype.equivFin (ShortWord w s))
        (shortField w (X σ)) (shortWeight w) Bs x t r).mp
      simpa only [← hBf, wf, Zf, shortIndex] using hB
    have hdet : frameDet (shortField w (X σ)) Bs x = frameDet (Zf σ) B x := rfl
    simpa only [hBf,hweights,hdet] using hgeometry x hx r hr hr1 hBs a b ha hae hb hbe v hv
  choose Φ hΦ hflow hgeometry using hfamily
  have hKU : K ⊆ ball x₀ (R / 4) := hKball.trans (ball_subset_ball (by linarith))
  have hKclosed : K ⊆ closedBall x₀ R :=
    hKball.trans ((ball_subset_ball (by linarith)).trans ball_subset_closedBall)
  have hKΩ : K ⊆ Ω := hKclosed.trans hRΩ
  have hZ : ∀ σ J, ContDiffOn ℝ (⊤ : ℕ∞) (Zf σ J) Ω :=
    fun σ J => shortField_contDiffOn hΩ (hX σ) (shortIndex w J)
  have hw : ∀ J : Fin m, (wf J : ℕ) ≤ s := fun J =>
    ((mem_shortWordFamily_iff w (shortIndex w J).val).mp (shortIndex w J).property).2
  have hspan : ∀ σ, ∀ x ∈ K, ∃ B : Fin n → Fin m, frameDet (Zf σ) B x ≠ 0 := by
    intro σ x hx
    obtain ⟨B, hB⟩ := hmax σ x (hKclosed hx)
    refine ⟨(Fintype.equivFin (ShortWord w s)) ∘ B, ?_⟩
    have hne := abs_pos.mp (hΔ.trans_le hB)
    simpa only [Zf, shortIndex, frameDet_reindex] using hne
  have hdata : ∀ σ, ∀ x ∈ K, ∀ B r, 0 < r → r ≤ 1 → IsSuboptimal (Zf σ) wf B x t r →
      ∀ v ∈ weightedBox wf (e * r),
        ChartAnalyticBounds Ω wf (Zf σ) B (fun u => Φ σ B ((Fin.append u v, x), 1))
          (weightedBox (wf ∘ B) (e * r)) r κ (2 * D₀ * t⁻¹ ^ n) ∧
        ChartTrajectories Ω (Zf σ) B (fun u => Φ σ B ((Fin.append u v, x), 1))
          (weightedBox (wf ∘ B) (e * r)) x v (fun u τ => Φ σ B ((Fin.append u v, x), τ)) ∧
        (v = 0 → Φ σ B ((Fin.append 0 v, x), 1) = x) :=
    fun σ x hx B r hr hr1 hB v hv => by
      have hd := hgeometry σ B x (hKball hx) r hr hr1 hB e e he le_rfl he le_rfl v hv
      exact ⟨hd.1,hd.2.1,hd.2.2.1⟩
  have hZjoint : ∀ J, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => Zf z.1 J z.2) (univ ×ˢ Ω) := fun J =>
    (shortField_joint_continuity_of_spatial_jets hΩ w X (fun σ _ => hX σ)
      hjoint (shortIndex w J)).1
  have hDZjoint : ∀ J, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => fderiv ℝ (Zf z.1 J) z.2) (univ ×ˢ Ω) := fun J =>
    (shortField_joint_continuity_of_spatial_jets hΩ w X (fun σ _ => hX σ)
      hjoint (shortIndex w J)).2
  let A : ℝ := wordJetBase n 1 s M ^ s
  have hA : 0 ≤ A := pow_nonneg (wordJetBase_nonneg_and_le hM).1 s
  have hshortjets : ∀ σ J, HasJetBound Ω (closedBall x₀ R) (Zf σ J) 1 A := by
    intro σ J
    have hlen : (shortIndex w J).val.length ≤ s :=
      (G3.length_le_weight w _).trans
        ((mem_shortWordFamily_iff w (shortIndex w J).val).mp (shortIndex w J).property).2
    exact wordBracket_jet_bound_uniform (h := 1) (L := s) hΩ hRΩ (X σ) (hX σ) hM
      (fun i => (hjets σ i).mono (by omega)) (shortIndex w J).val hlen
  have hvalue : ∀ σ, ∀ y ∈ closedBall x₀ R, ∀ J, ‖Zf σ J y‖ ≤ A := by
    intro σ y hy J
    simpa only [norm_iteratedFDerivWithin_zero] using (hshortjets σ J) 0 (by omega) y hy
  have hder : ∀ σ, ∀ y ∈ closedBall x₀ R, ∀ J, ‖fderiv ℝ (Zf σ J) y‖ ≤ A := by
    intro σ y hy J
    have hb : HasJetBound Ω (closedBall x₀ R) (fderiv ℝ (Zf σ J)) 0 A :=
      (hshortjets σ J).fderiv hΩ hRΩ
    simpa only [norm_iteratedFDerivWithin_zero] using hb 0 le_rfl y hy
  have hindices : ∀ B : Fin n → Fin m, ∀ j : Fin (n + m),
      selectedAuxiliaryIndex w (shortIndex w ∘ B) j = shortIndex w (Fin.addCases B id j) := by
    intro B j
    have hBf : (Fintype.equivFin (ShortWord w s)) ∘ (shortIndex w ∘ B) = B := by
      funext i
      simp [shortIndex]
    simpa only [hBf] using
      (shortIndex_selectedAuxiliaryIndex w (shortIndex w ∘ B) j).symm
  have hinit : ∀ σ B, ∀ p ∈ ball 0 δ ×ˢ ball x₀ (R / 4), Φ σ B (p, 0) = p.2 :=
    fun σ B p hp => (hflow σ B p.1 hp.1 p.2 hp.2).1
  have hrange : ∀ σ B, ∀ p ∈ ball 0 δ ×ˢ ball x₀ (R / 4),
      ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ σ B (p, τ) ∈ closedBall x₀ R :=
    fun σ B p hp τ hτ => ball_subset_closedBall ((hflow σ B p.1 hp.1 p.2 hp.2).2 τ hτ).1
  have hode : ∀ σ B, ∀ p ∈ ball 0 δ ×ˢ ball x₀ (R / 4), ∀ τ ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun v => Φ σ B (p, v))
        (∑ j, p.1 j • Zf σ (Fin.addCases B id j) (Φ σ B (p, τ))) τ := by
    intro σ B p hp τ hτ
    simpa only [hindices, Zf] using ((hflow σ B p.1 hp.1 p.2 hp.2).2 τ hτ).2
  have hD : 0 < 2 * D₀ * t⁻¹ ^ n := by positivity
  obtain ⟨r₀, c, hr₀, hr₀1, hc, hce, hinj⟩ :=
    exists_compact_uniform_parameter_selected_flow_chart_injectivity
      hΩ isOpen_ball hRΩ (isCompact_closedBall x₀ R) (convex_closedBall x₀ R)
      hK hKU hKΩ wf hw Zf hZ hZjoint hDZjoint (he.trans heδ) hA hA hvalue hder
      Φ hΦ hinit hrange hode he he1 hD.le hκ.le hsmall ht ht1 hdata hspan
  refine ⟨Φ, 2 * D₀ * t⁻¹ ^ n, κ, r₀, c, hD, hκ, hsmall,
    hr₀, hr₀1, hc, hce.trans he1, ?_, ?_⟩
  · exact fun σ B => ⟨hΦ σ B, hflow σ B⟩
  · intro σ x hx r hr hrr B hB v hv F Γ
    have hresult := hgeometry σ B x (hKball hx) r hr (hrr.trans hr₀1) hB
      c c hc hce hc hce v hv
    exact ⟨hinj σ x hx r hr hrr B hB v hv, hresult.1, hresult.2.1,
      hresult.2.2.1,hresult.2.2.2⟩

end RothschildStein.G4
