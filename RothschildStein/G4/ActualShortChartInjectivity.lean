-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedChartDataWithJacobian
public import RothschildStein.G4.CompactUniformChartInjectivity
public import RothschildStein.G4.SelectedChartDerivativeContinuity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- For a fixed smooth system, primitive jet and rank bounds
construct a common actual shifted chart family with uniform compact-center
injectivity. The analytic and trajectory bounds concern the same maps;
no derivative-continuity or injectivity premise is supplied by the caller
(BB Theorems 9.11/9.42, pp. 404, 438). -/
theorem exists_actual_short_chart_injectivity (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) {M Δ R t : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) (ht : 0 < t) (ht1 : t < 1)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (hstep : bracketStepOn Ω w X s)
    (x₀ : Fin n → ℝ) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
      (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M)
    (hmax : ∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
      Δ ≤ |frameDet (shortField w X) B y|) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun j => shortField w X (shortIndex w j)
    ∃ a r₀ D κ : ℝ, 0 < a ∧ a < 1 ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      0 ≤ D ∧ 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∃ Φ : (Fin n → ShortWord w s) →
        (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ∀ x ∈ closedBall x₀ (R / 16), ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → ShortWord w s,
        IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ v ∈ weightedBox wf (a * r),
      let F := fun u => Φ B ((Fin.append u v, x), 1)
      let Q := weightedBox (shortWeight w ∘ B) (a * r)
      ChartAnalyticBounds Ω wf Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q r κ D ∧
      ChartTrajectories Ω Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q x v
        (fun u τ => Φ B ((Fin.append u v, x), τ)) ∧
      (v = 0 → F 0 = x) ∧ InjOn F Q ∧
      ∀ u ∈ Q, |frameDet (shortField w X) B x| / 4 ≤
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
          4 * |frameDet (shortField w X) B x| := by
  intro m wf Zf
  classical
  obtain ⟨D, hD, κ, hκ, hκsmall, hprovider⟩ :=
    exists_uniform_selected_chart_data_with_jacobian k n s h q hn hs horder hq w M Δ R hM hΔ hR
  obtain ⟨e, he, he1, het, heδ, hcharts⟩ := hprovider t ht ht1.le
  let δ := R / (64 * (1 + ((n + m : ℕ) : ℝ) * wordJetBase n 0 s M ^ s))
  have hδ : 0 < δ := he.trans heδ
  choose Φ hΦ hODE hgeom using hcharts Ω hΩ X hX hstep x₀ hRΩ hjets hmax
  let P := ↥(closedBall x₀ (R / 16))
  let centerCompactSpace : CompactSpace P :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall x₀ (R / 16))
  have hcenter : ∀ p : P, p.val ∈ ball x₀ (R / 8) := by
    intro p
    exact closedBall_subset_ball (by linarith) p.property
  have hcenterΩ : ∀ p : P, p.val ∈ Ω := fun p =>
    hRΩ (closedBall_subset_closedBall (by linarith) p.property)
  let Z : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun _ => Zf
  let F : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun p B v u => Φ (shortIndex w ∘ B) ((Fin.append u v, p.val), 1)
  let Γ : P → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ) :=
    fun p B v u τ => Φ (shortIndex w ∘ B) ((Fin.append u v, p.val), τ)
  let D₀ := 2 * D * t⁻¹ ^ n
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hweights (B : Fin n → Fin m) : shortWeight w ∘ (shortIndex w ∘ B) = wf ∘ B := rfl
  have hback (B : Fin n → Fin m) :
      (Fintype.equivFin (ShortWord w s)) ∘ (shortIndex w ∘ B) = B := by
    funext j
    simp [shortIndex, Function.comp_def]
  have hforward (C : Fin n → ShortWord w s) :
      shortIndex w ∘ ((Fintype.equivFin (ShortWord w s)) ∘ C) = C := by
    funext j
    simp [shortIndex, Function.comp_def]
  have hdetback (C : Fin n → Fin m) (y : Fin n → ℝ) :
      frameDet Zf C y = frameDet (shortField w X) (shortIndex w ∘ C) y := rfl
  have hfwback (C : Fin n → Fin m) :
      frameWeight wf C = frameWeight (shortWeight w) (shortIndex w ∘ C) := rfl
  have hdata : ∀ p ∈ (univ : Set P), ∀ B r, 0 < r → r ≤ 1 →
      IsSuboptimal (Z p) wf B p.val t r → ∀ v ∈ weightedBox wf (e * r),
      ChartAnalyticBounds Ω wf (Z p) B (F p B v) (weightedBox (wf ∘ B) (e * r)) r κ D₀ ∧
      ChartTrajectories Ω (Z p) B (F p B v) (weightedBox (wf ∘ B) (e * r)) p.val v (Γ p B v) ∧
      (v = 0 → F p B v 0 = p.val) := by
    intro p _ B r hr hr1 hB v hv
    have hsub : IsSuboptimal (shortField w X) (shortWeight w) (shortIndex w ∘ B) p.val t r := by
      intro C
      have hh := hB ((Fintype.equivFin (ShortWord w s)) ∘ C)
      change t * (|frameDet Zf ((Fintype.equivFin (ShortWord w s)) ∘ C) p.val| *
        r ^ frameWeight wf ((Fintype.equivFin (ShortWord w s)) ∘ C)) ≤
        |frameDet Zf B p.val| * r ^ frameWeight wf B at hh
      rw [hdetback, hfwback, hforward, hdetback, hfwback] at hh
      exact hh
    have hd := hgeom (shortIndex w ∘ B) p.val (hcenter p) r hr hr1 hsub
      e e he le_rfl he le_rfl v hv
    have hd' := And.intro hd.1 (And.intro hd.2.1 hd.2.2.1)
    simpa only [hweights, hback, Z, F, Γ, D₀] using hd'
  have hcont : ∀ J, Continuous (fun p : P => Z p J p.val) := by
    intro J
    exact (shortField_contDiffOn hΩ hX (shortIndex w J)).continuousOn.comp_continuous
      continuous_subtype_val hcenterΩ
  have hspan : ∀ p ∈ (univ : Set P), ∃ B : Fin n → Fin m, frameDet (Z p) B p.val ≠ 0 := by
    intro p _
    obtain ⟨B, hB⟩ := hmax p.val (closedBall_subset_closedBall (by linarith) p.property)
    refine ⟨(Fintype.equivFin (ShortWord w s)) ∘ B, ?_⟩
    have hnz := abs_pos.mp (hΔ.trans_le hB)
    simpa only [Z, Zf, shortIndex, frameDet_reindex] using hnz
  have hlocal : ∀ p ∈ (univ : Set P), ∀ B : Fin n → Fin m,
      ∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p), DifferentiableAt ℝ (F q.2 B 0) q.1 := by
    intro p _ B
    have ha : Continuous (fun q : (Fin n → ℝ) × P => Fin.append q.1 (0 : Fin m → ℝ)) := by
      have hh : Continuous (fun q : (Fin n → ℝ) × P =>
          (selectedCoefficientInclusion n m) q.1) :=
        (selectedCoefficientInclusion n m).continuous.comp continuous_fst
      convert hh using 1
      funext q
      rw [selectedCoefficient_append_affine]
      have hzero : Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ) = 0 := by
        ext j
        exact Fin.addCases (fun j => by simp) (fun j => by simp) j
      rw [hzero, add_zero]
    have hm : ∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p),
        Fin.append q.1 (0 : Fin m → ℝ) ∈ ball 0 δ :=
      ha.continuousAt.preimage_mem_nhds (by
        have hzero : Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ) = 0 := by
          ext j
          exact Fin.addCases (fun j => by simp) (fun j => by simp) j
        rw [hzero]
        exact isOpen_ball.mem_nhds (mem_ball_self hδ))
    filter_upwards [hm] with q hq
    exact (timeOne_selected_slice_contDiffAt isOpen_ball (Φ (shortIndex w ∘ B))
      (hΦ _) q.1 0 hq (ball_subset_ball (by linarith) (hcenter q.2))).differentiableAt (by simp)
  have hder : ∀ p ∈ (univ : Set P), ∀ B : Fin n → Fin m,
      ContinuousAt (fun q : (Fin n → ℝ) × P => fderiv ℝ (F q.2 B 0) q.1) (0, p) := by
    intro p _ B
    have hd := selected_chart_fderiv_continuousAt_zero isOpen_ball hδ
      (Φ (shortIndex w ∘ B)) (hΦ _) (ball_subset_ball (by linarith) (hcenter p))
    have hm : ContinuousAt (fun q : (Fin n → ℝ) × P => (q.1, q.2.val)) (0, p) :=
      continuousAt_fst.prodMk (continuous_subtype_val.continuousAt.comp continuousAt_snd)
    exact hd.comp (f := fun q : (Fin n → ℝ) × P => (q.1, q.2.val)) hm
  have hw : ∀ J, (wf J : ℕ) ≤ s := fun J =>
    ((mem_shortWordFamily_iff w (shortIndex w J).val).mp (shortIndex w J).property).2
  obtain ⟨r₀, c, hr₀, hr1, hc, hce, hinj⟩ :=
    exists_compact_uniform_chart_injectivity_of_actual_derivative_continuity isCompact_univ
      wf hw Z Ω (fun _ _ J => (shortField_contDiffOn hΩ hX (shortIndex w J)).continuousOn)
      F Γ Subtype.val he he1 hD₀ hκ.le hκsmall ht ht1 hdata hcont hspan hlocal hder
  refine ⟨c, r₀, D₀, κ, hc, (hce.trans het).trans_lt ht1, hr₀, hr1, hD₀, hκ, hκsmall, Φ, ?_⟩
  intro x hx r hr hrr B hB v hv
  let p : P := ⟨x, hx⟩
  have hsmall := hgeom B x (hcenter p) r hr (hrr.trans hr1) hB c c hc hce hc hce v hv
  have hsubfin : IsSuboptimal (Z p) wf
      ((Fintype.equivFin (ShortWord w s)) ∘ B) p.val t r := by
    intro C
    have hh := hB (shortIndex w ∘ C)
    change t * (|frameDet Zf C x| * r ^ frameWeight wf C) ≤
      |frameDet Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) x| *
        r ^ frameWeight wf ((Fintype.equivFin (ShortWord w s)) ∘ B)
    rw [hdetback, hfwback, hdetback, hfwback, hforward]
    exact hh
  have hi := hinj p (mem_univ _) r hr hrr
    ((Fintype.equivFin (ShortWord w s)) ∘ B) hsubfin v hv
  have hBB : shortIndex w ∘ ((Fintype.equivFin (ShortWord w s)) ∘ B) = B := by
    funext j
    simp [shortIndex, Function.comp_def]
  refine ⟨hsmall.1, hsmall.2.1, hsmall.2.2.1, ?_, hsmall.2.2.2⟩
  simpa [F, hBB, p, wf, shortIndex, Function.comp_def] using hi

end RothschildStein.G4
