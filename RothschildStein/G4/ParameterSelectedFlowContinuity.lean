-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterSelectedChartRegularity
public import RothschildStein.G4.ParameterLinearFlowDerivativeContinuity
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Actual signed coefficient-linear flows give joint selected
chart derivative continuity at time 1, with continuous external parameters.
The spatial derivative of the flow is derived from its ODE and the actual
field budgets (BB Props. 9.53–9.54, p. 452). -/
theorem parameter_selected_flow_chart_local_regularity {Sg : Type*} {n m : ℕ}
    [UniformSpace Sg] [LocallyCompactSpace Sg]
    {Ω L U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hLΩ : L ⊆ Ω) (hLc : IsCompact L) (hL : Convex ℝ L)
    {δ D M : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (Y : Sg → Fin (n + m) → (Fin n → ℝ) → (Fin n → ℝ))
    (hY : ∀ σ J, ContDiffOn ℝ (⊤ : ℕ∞) (Y σ J) Ω)
    (hYjoint : ∀ J, ContinuousOn (fun q : Sg × (Fin n → ℝ) => Y q.1 J q.2) (univ ×ˢ Ω))
    (hDYjoint : ∀ J, ContinuousOn (fun q : Sg × (Fin n → ℝ) =>
      fderiv ℝ (Y q.1 J) q.2) (univ ×ˢ Ω))
    (hvalue : ∀ σ, ∀ y ∈ L, ∀ J, ‖Y σ J y‖ ≤ M)
    (hder : ∀ σ, ∀ y ∈ L, ∀ J, ‖fderiv ℝ (Y σ J) y‖ ≤ D)
    (Φ : Sg → (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ σ, ContDiffOn ℝ (⊤ : ℕ∞) (Φ σ) ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    (hinit : ∀ σ, ∀ p ∈ ball 0 δ ×ˢ U, Φ σ (p, 0) = p.2)
    (hrange : ∀ σ, ∀ p ∈ ball 0 δ ×ˢ U, ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ σ (p, τ) ∈ L)
    (hode : ∀ σ, ∀ p ∈ ball 0 δ ×ˢ U, ∀ τ ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun v => Φ σ (p, v)) (∑ J, p.1 J • Y σ J (Φ σ (p, τ))) τ)
    (p : Sg × (Fin n → ℝ)) (hp : p.2 ∈ U) :
    (∀ᶠ q : (Fin n → ℝ) × (Sg × (Fin n → ℝ)) in 𝓝 (0, p),
      DifferentiableAt ℝ (fun u => Φ q.2.1 ((Fin.append u 0, q.2.2), 1)) q.1) ∧
    ContinuousAt (fun q : (Fin n → ℝ) × (Sg × (Fin n → ℝ)) =>
      fderiv ℝ (fun u => Φ q.2.1 ((Fin.append u 0, q.2.2), 1)) q.1) (0, p) := by
  let V : Set ((Fin (n + m) → ℝ) × (Fin n → ℝ)) := ball 0 δ ×ˢ U
  have hV : IsOpen V := isOpen_ball.prod hU
  have hcoef : ∀ a ∈ closedBall (0 : Fin (n + m) → ℝ) δ, ‖a‖ ≤ δ := by
    intro a ha
    simpa only [mem_closedBall, dist_zero_right] using ha
  have hDf := parameter_linear_flow_state_derivative_joint_continuousOn
    (U := (univ : Set Sg)) isOpen_univ hΩ hLΩ hV
    (isCompact_closedBall (0 : Fin (n + m) → ℝ) δ) hLc
    (convex_closedBall (0 : Fin (n + m) → ℝ) δ) hL
    (fun q hq => ball_subset_closedBall hq.1) Y (fun σ _ => hY σ) hYjoint hDYjoint
    hδ.le hD hM (show (0 : ℝ) < 3 / 2 by norm_num) (show (3 / 2 : ℝ) < 2 by norm_num)
    hcoef (fun σ _ => hvalue σ) (fun σ _ => hder σ) Φ
    (fun σ _ => hinit σ) (fun σ _ => hrange σ) (fun σ _ => hode σ)
  let F : Sg → ((Fin (n + m) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
    fun σ z => Φ σ (z, 1)
  have hF : ∀ σ, ContDiffOn ℝ (⊤ : ℕ∞) (F σ) V := by
    intro σ
    apply (hΦ σ).comp (contDiff_id.prodMk contDiff_const).contDiffOn
    intro z hz
    exact ⟨hz, by constructor <;> norm_num⟩
  have hmap : MapsTo (fun q : Sg × ((Fin (n + m) → ℝ) × (Fin n → ℝ)) => ((q.1, q.2), (1 : ℝ)))
      (univ ×ˢ V) ((univ ×ˢ V) ×ˢ Ioo (-(3 / 2 : ℝ)) (3 / 2)) := by
    intro q hq
    exact ⟨hq, by constructor <;> norm_num⟩
  have hDstate : ContinuousOn (fun q : Sg × ((Fin (n + m) → ℝ) × (Fin n → ℝ)) =>
      fderiv ℝ (F q.1) q.2) (univ ×ˢ V) :=
    hDf.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hzero : Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ) = 0 := by
    ext j
    exact Fin.addCases (fun i => by simp) (fun i => by simp) j
  have hpoint : (Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ), p.2) ∈ V := by
    refine ⟨?_, hp⟩
    rw [hzero, mem_ball, dist_self]
    exact hδ
  exact parameter_selected_chart_local_regularity isOpen_univ hV F
    (fun σ _ z hz => ((hF σ).contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))
    hDstate Prod.fst Prod.snd continuous_fst continuous_snd p (mem_univ _) hpoint

end RothschildStein.G4
