-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ParameterCompactSpatialCharts
public import RothschildStein.G4.ShiftedBallBoxFromChart
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.G4

/-- The full shifted ball-box, Jacobian and smooth weighted-inverse
package on arbitrary compact spatial patches, uniformly over compact
external families (BB Theorem 9.42, p. 438). -/
theorem exists_parameter_compact_spatial_ball_box {Sg : Type*}
    [UniformSpace Sg] [CompactSpace Sg] (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (Ω K : Set (Fin n → ℝ))
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : Sg → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ j, ContDiffOn ℝ (⊤ : ℕ∞) (X σ j) Ω)
    (hstep : ∀ σ, bracketStepOn Ω w (X σ) s)
    (hjoint : ∀ J, ∀ i ≤ max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)),
      ContinuousOn (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2)
        (univ ×ˢ Ω))
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Sg → Fin m → (Fin n → ℝ) → (Fin n → ℝ) :=
      fun σ j => shortField w (X σ) (shortIndex w j)
    ∃ a b r₀ D κ : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ D ∧ 0 < κ ∧ (n : ℝ)*κ ≤ 1/4 ∧
      ∃ Φ : (Fin n → ℝ) → Sg → (Fin n → Fin m) →
        (((Fin (n+m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B, IsSuboptimal (Zf σ) wf B x t r → ∀ v ∈ weightedBox wf (b*r),
      let F := fun u => Φ x σ B ((Fin.append u v,x),1)
      let Q := weightedBox (wf ∘ B) (a*r)
      ChartAnalyticBounds Ω wf (Zf σ) B F Q r κ D ∧
      ChartTrajectories Ω (Zf σ) B F Q x v (fun u τ => Φ x σ B ((Fin.append u v,x),τ)) ∧
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
  obtain ⟨A⟩ := exists_parameter_compact_spatial_charts k n s h q hn hs horder hq
    w Ω K hΩ hK hKΩ X hX hstep hjoint t ht ht1
  let a := A.c/2
  have ha : 0 < a := half_pos A.c_pos
  have hac : a ≤ A.c := half_le_self A.c_pos.le
  have ha1 : a < 1 := by have hh := A.c_le_one; dsimp [a]; linarith
  obtain ⟨b,hb,hba,hb1,hball⟩ := exists_shifted_ball_box_radius
    (m := m) (n := n) (s := s) ha ha1.le A.D_pos.le
  refine ⟨a,b,A.r₀,A.D,A.κ,ha,ha1,hb,hba,hb1,A.radius_pos,A.radius_le_one,
    A.D_pos.le,A.κ_pos,A.κ_small,A.Φ,?_⟩
  intro σ x hx r hr hrr B hB v hv F Q
  have hbc : b ≤ A.c := by linarith
  have hvC := weightedBox_subset_of_radius_le wf (mul_nonneg hb.le hr.le)
    (mul_le_mul_of_nonneg_right hbc hr.le) hv
  obtain ⟨hinj,hAB,htraj,hzero,hjac⟩ := A.charts σ x hx r hr hrr B hB v hvC
  have hQC : Q ⊆ weightedBox (wf ∘ B) (A.c*r) :=
    weightedBox_subset_of_radius_le (wf ∘ B) (mul_nonneg ha.le hr.le)
      (mul_le_mul_of_nonneg_right hac hr.le)
  have hAB' := chartAnalyticBounds_mono hAB hQC
  have htraj' := chartTrajectories_mono htraj hQC
  have hinj' := hinj.mono hQC
  have hw : ∀ i, (wf (B i) : ℕ) ≤ s := fun i =>
    ((mem_shortWordFamily_iff w (shortIndex w (B i)).val).mp (shortIndex w (B i)).property).2
  have hspan : ∃ C : Fin n → Fin m, frameDet (Zf σ) C x ≠ 0 := by
    obtain ⟨C,hC⟩ := exists_short_frame (hstep σ) (hKΩ hx)
    refine ⟨(Fintype.equivFin (ShortWord w s)) ∘ C,?_⟩
    simpa only [Zf,shortIndex,frameDet_reindex] using hC
  have hBx := suboptimal_frame_ne_zero ht hr hspan hB
  have hresult := hball wf (Zf σ) B hw Ω x F
    (fun u τ => A.Φ x σ B ((Fin.append u v,x),τ)) r A.κ hr
    (hrr.trans A.radius_le_one) A.κ_pos.le A.κ_small v hv hBx hAB' htraj' hinj'
  exact ⟨hAB',htraj',hzero,hinj',fun u hu => hjac u (hQC hu),hresult⟩
end RothschildStein.G4
