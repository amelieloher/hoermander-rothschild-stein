-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterSelectedFlowContinuity
public import RothschildStein.G4.CompactUniformChartInjectivity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Compact external families of actual finite selected flows
have one shifted-chart injectivity threshold over a compact initial-point
set. Actual derivative continuity is proved from field continuity, budgets
and the ODE; no external-parameter derivative is assumed (BB pp. 450–458). -/
theorem exists_compact_uniform_parameter_selected_flow_chart_injectivity
    {Sg : Type*} [UniformSpace Sg] [CompactSpace Sg] {m n s : ℕ}
    {Ω L U K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hLΩ : L ⊆ Ω) (hLc : IsCompact L) (hL : Convex ℝ L)
    (hK : IsCompact K) (hKU : K ⊆ U) (hKΩ : K ⊆ Ω)
    (w : Fin m → ℕ+) (hw : ∀ J, (w J : ℕ) ≤ s)
    (Z : Sg → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hZ : ∀ σ J, ContDiffOn ℝ (⊤ : ℕ∞) (Z σ J) Ω)
    (hZjoint : ∀ J, ContinuousOn (fun q : Sg × (Fin n → ℝ) => Z q.1 J q.2) (univ ×ˢ Ω))
    (hDZjoint : ∀ J, ContinuousOn (fun q : Sg × (Fin n → ℝ) =>
      fderiv ℝ (Z q.1 J) q.2) (univ ×ˢ Ω))
    {δ D₁ M a D κ t : ℝ} (hδ : 0 < δ) (hD₁ : 0 ≤ D₁) (hM : 0 ≤ M)
    (hvalue : ∀ σ, ∀ y ∈ L, ∀ J, ‖Z σ J y‖ ≤ M)
    (hder : ∀ σ, ∀ y ∈ L, ∀ J, ‖fderiv ℝ (Z σ J) y‖ ≤ D₁)
    (Φ : Sg → (Fin n → Fin m) →
      (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ σ B, ContDiffOn ℝ (⊤ : ℕ∞) (Φ σ B) ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    (hinit : ∀ σ B, ∀ p ∈ ball 0 δ ×ˢ U, Φ σ B (p, 0) = p.2)
    (hrange : ∀ σ B, ∀ p ∈ ball 0 δ ×ˢ U, ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ σ B (p, τ) ∈ L)
    (hode : ∀ σ B, ∀ p ∈ ball 0 δ ×ˢ U, ∀ τ ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun v => Φ σ B (p, v))
        (∑ J, p.1 J • Z σ (Fin.addCases B id J) (Φ σ B (p, τ))) τ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D)
    (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4) (ht : 0 < t) (ht1 : t < 1)
    (hdata : ∀ σ, ∀ x ∈ K, ∀ B r, 0 < r → r ≤ 1 → IsSuboptimal (Z σ) w B x t r →
      ∀ v ∈ weightedBox w (a * r),
        ChartAnalyticBounds Ω w (Z σ) B (fun u => Φ σ B ((Fin.append u v, x), 1))
          (weightedBox (w ∘ B) (a * r)) r κ D ∧
        ChartTrajectories Ω (Z σ) B (fun u => Φ σ B ((Fin.append u v, x), 1))
          (weightedBox (w ∘ B) (a * r)) x v (fun u τ => Φ σ B ((Fin.append u v, x), τ)) ∧
        (v = 0 → Φ σ B ((Fin.append 0 v, x), 1) = x))
    (hspan : ∀ σ, ∀ x ∈ K, ∃ B : Fin n → Fin m, frameDet (Z σ) B x ≠ 0) :
    ∃ r₀ c : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 < c ∧ c ≤ a ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B, IsSuboptimal (Z σ) w B x t r →
      ∀ v ∈ weightedBox w (c * r),
        InjOn (fun u => Φ σ B ((Fin.append u v, x), 1)) (weightedBox (w ∘ B) (c * r)) := by
  let compactInitialPointSpace : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (Sg × K) → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun p B v u => Φ p.1 B ((Fin.append u v, p.2.val), 1)
  let Γ : (Sg × K) → (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ) :=
    fun p B v u τ => Φ p.1 B ((Fin.append u v, p.2.val), τ)
  have hcolumns : ∀ J, Continuous (fun p : Sg × K => Z p.1 J p.2.val) := by
    intro J
    apply continuousOn_univ.mp
    apply (hZjoint J).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p _hp
    exact ⟨mem_univ _, hKΩ p.2.property⟩
  have hregular : ∀ p : Sg × K, ∀ B : Fin n → Fin m,
      (∀ᶠ q : (Fin n → ℝ) × (Sg × K) in 𝓝 (0, p), DifferentiableAt ℝ (F q.2 B 0) q.1) ∧
      ContinuousAt (fun q : (Fin n → ℝ) × (Sg × K) => fderiv ℝ (F q.2 B 0) q.1) (0, p) := by
    intro p B
    let Y : Sg → Fin (n + m) → (Fin n → ℝ) → (Fin n → ℝ) :=
      fun σ J => Z σ (Fin.addCases B id J)
    have hYs : ∀ σ J, ContDiffOn ℝ (⊤ : ℕ∞) (Y σ J) Ω := by
      intro σ J
      exact hZ σ (Fin.addCases B id J)
    have hYc : ∀ J, ContinuousOn (fun q : Sg × (Fin n → ℝ) => Y q.1 J q.2) (univ ×ˢ Ω) := by
      intro J
      exact hZjoint (Fin.addCases B id J)
    have hYDc : ∀ J, ContinuousOn (fun q : Sg × (Fin n → ℝ) =>
        fderiv ℝ (Y q.1 J) q.2) (univ ×ˢ Ω) := by
      intro J
      exact hDZjoint (Fin.addCases B id J)
    have hYv : ∀ σ, ∀ y ∈ L, ∀ J, ‖Y σ J y‖ ≤ M := by
      intro σ y hy J
      exact hvalue σ y hy (Fin.addCases B id J)
    have hYD : ∀ σ, ∀ y ∈ L, ∀ J, ‖fderiv ℝ (Y σ J) y‖ ≤ D₁ := by
      intro σ y hy J
      refine Fin.addCases ?_ ?_ J
      · intro i
        simpa only [Y, Fin.addCases_left] using hder σ y hy (B i)
      · intro i
        simpa only [Y, Fin.addCases_right, id_eq] using hder σ y hy i
    have hr := parameter_selected_flow_chart_local_regularity (Sg := Sg) (n := n) (m := m)
      (Ω := Ω) (L := L) (U := U) (δ := δ) (D := D₁) (M := M)
      hΩ hU hLΩ hLc hL hδ hD₁ hM Y hYs hYc hYDc hYv hYD
      (fun σ => Φ σ B) (fun σ => hΦ σ B) (fun σ => hinit σ B)
      (fun σ => hrange σ B) (fun σ => hode σ B) (p.1, p.2.val) (hKU p.2.property)
    have hi : Continuous (fun q : (Fin n → ℝ) × (Sg × K) => (q.1, (q.2.1, q.2.2.val))) :=
      continuous_fst.prodMk
        (continuous_snd.fst.prodMk (continuous_subtype_val.comp continuous_snd.snd))
    have hloc : ∀ᶠ q : (Fin n → ℝ) × (Sg × K) in 𝓝 (0, p),
        DifferentiableAt ℝ (fun u => Φ q.2.1 B ((Fin.append u 0, q.2.2.val), 1)) q.1 :=
      (hi.tendsto (0, p)).eventually hr.1
    exact ⟨hloc,
      hr.2.comp (f := fun q : (Fin n → ℝ) × (Sg × K) => (q.1, (q.2.1, q.2.2.val)))
        (x := (0, p)) hi.continuousAt⟩
  obtain ⟨r₀, c, hr₀, hr₀1, hc, hca, hinj⟩ :=
    exists_compact_uniform_chart_injectivity_of_actual_derivative_continuity
      (K := (univ : Set (Sg × K))) isCompact_univ w hw (fun p => Z p.1) Ω
      (fun p _ J => (hZ p.1 J).continuousOn) F Γ (fun p => p.2.val)
      ha ha1 hD hκ hsmall ht ht1 (fun p _ => hdata p.1 p.2.val p.2.property)
      hcolumns (fun p _ => hspan p.1 p.2.val p.2.property)
      (fun p _ B => (hregular p B).1) (fun p _ B => (hregular p B).2)
  refine ⟨r₀, c, hr₀, hr₀1, hc, hca, ?_⟩
  intro σ x hx r hr hrr B hB v hv
  exact hinj (σ, ⟨x, hx⟩) (mem_univ _) r hr hrr B hB v hv

end RothschildStein.G4
