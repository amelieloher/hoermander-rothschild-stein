-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CompactParameterJetBudget
public import RothschildStein.G4.CompactParameterRankFloor
public import RothschildStein.G4.ContinuousShortFieldJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.G4

/-- Every spatial center has a compact convex buffer with uniform
external-family jet and rank budgets; no single ball containing the entire
spatial patch is required (BB p. 452). -/
theorem exists_parameter_local_buffer {P : Type*} [TopologicalSpace P]
    [CompactSpace P] {m n s : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ p i, ContDiffOn ℝ (⊤ : ℕ∞) (X p i) Ω)
    (hstep : ∀ p, bracketStepOn Ω w (X p) s)
    (H : ℕ) (hH : s + 1 ≤ H)
    (hj : ∀ i, ∀ j ≤ H, ContinuousOn
      (fun z : P × (Fin n → ℝ) => iteratedFDeriv ℝ j (X z.1 i) z.2)
      (univ ×ˢ Ω)) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R Δ M : ℝ, 0 < R ∧ 0 < Δ ∧ 0 < M ∧ closedBall z R ⊆ Ω ∧
      (∀ p i, HasJetBound Ω (closedBall z R) (X p i) H M) ∧
      ∀ p y, y ∈ closedBall z R → ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w (X p)) B y| := by
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  let R := d / 2
  have hR : 0 < R := half_pos hd
  have hRΩ : closedBall z R ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hd)).trans hball
  obtain ⟨M, hM, hjet⟩ := exists_compact_parameter_jet_budget hΩ
    (isCompact_closedBall z R) hRΩ X H hj
  obtain ⟨Δ, hΔ, hrank⟩ := exists_compact_parameter_rank_floor
    (isCompact_closedBall z R) (fun p => shortField w (X p))
    (fun I => (shortField_joint_continuity_of_spatial_jets hΩ w X
      (fun p _ i => hX p i) (fun i j hj' => hj i j (hj'.trans hH)) I).1.mono
        (Set.prod_mono Subset.rfl hRΩ))
    (fun p y hy => exists_short_frame (hstep p) (hRΩ hy))
  exact ⟨R, Δ, M, hR, hΔ, hM, hRΩ, hjet, hrank⟩

end RothschildStein.G4
