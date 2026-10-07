-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.JointChartInverseBound
public import RothschildStein.P1.JointModelTransport
public import RothschildStein.P1.KernelEstimatesWeightedTaylor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- On a fixed compact center patch, all actual
near-pole inverse endpoints lie in one compact parameter set. -/
theorem exists_inputModel_near_parameter_range
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ δ : ℝ, ∃ L : Set (Fin (n + m) → ℝ), 0 < δ ∧ δ ≤ 1 ∧
      IsCompact L ∧ K ⊆ L ∧ ∀ ξ ∈ K, ∀ u, kgauge C.G u ≤ δ → (C.e ξ).symm (-u) ∈ L := by
  obtain ⟨ρ, M, hρ, _, hb⟩ := C.exists_inverse_zero_bound hK hKU
  let S := K ×ˢ closedBall (0 : Fin (n + m) → ℝ) ρ
  let I := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.e p.1).symm (-p.2)
  have hm : MapsTo (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, -p.2)) S C.T := by
    intro p hp
    refine ⟨hKU hp.1, (hb p.1 hp.1 (-p.2) ?_).1⟩
    simpa only [mem_closedBall, dist_zero_right, norm_neg] using hp.2
  have hI : IsCompact (I '' S) := (hK.prod (isCompact_closedBall (0 : Fin (n + m) → ℝ) ρ)).image_of_continuousOn
    (C.inverse_joint_contDiffOn.continuousOn.comp
      (continuous_fst.prodMk continuous_snd.neg).continuousOn hm)
  refine ⟨min ρ 1, K ∪ I '' S, lt_min hρ zero_lt_one, min_le_right _ _, hK.union hI,
    subset_union_left, ?_⟩
  intro ξ hξ u hu
  right
  refine ⟨(ξ, u), ⟨hξ, ?_⟩, rfl⟩
  have hn : ‖u‖ ≤ ρ := (norm_le_kgauge C.G (hu.trans (min_le_right _ _))).trans
    (hu.trans (min_le_left _ _))
  simpa only [mem_closedBall, dist_zero_right] using hn

/-- The full reflected chart density is uniformly
bounded on each compact center patch and fixed model gauge ball. -/
theorem exists_reflectedTransport_near_bound
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) (δ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ ∈ K, ∀ u, kgauge C.G u ≤ δ → ‖C.reflectedTransport ξ ψ u‖ ≤ B := by
  have hc : ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.reflectedTransport p.1 ψ p.2)
      (K ×ˢ {u | kgauge C.G u ≤ δ}) :=
    (C.reflectedTransport_joint_contDiffOn ψ).continuousOn.mono (fun p hp => ⟨hKU hp.1, mem_univ _⟩)
  obtain ⟨B, hb⟩ := (hK.prod (G2.isCompact_gauge_sublevel C.G δ)).exists_bound_of_continuousOn hc
  exact ⟨max B 0, le_max_right _ _, fun ξ hξ u hu => (hb (ξ, u) ⟨hξ, hu⟩).trans (le_max_left _ _)⟩

end RothschildStein.P1.LiftedChart
