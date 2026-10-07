-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalFrame
public import RothschildStein.G1.JetBounds
public import RothschildStein.G4.FiniteJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.G4

/-- Smooth bracket-generating coefficients supply a
positive rank buffer and every required finite jet budget locally.
The bounds are conclusions, not additional geometric premises
(BB Theorem 9.12, pp. 405–406). -/
theorem exists_actual_local_frame_buffer {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (H : ℕ)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R Δ M : ℝ, 0 < R ∧ 0 < Δ ∧ 0 < M ∧
      closedBall z R ⊆ Ω ∧
      (∀ i, HasJetBound Ω (closedBall z R) (X i) H M) ∧
      ∀ y ∈ closedBall z R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y| := by
  obtain ⟨B, hB⟩ := exists_short_frame hstep hz
  let Δ := |frameDet (shortField w X) B z| / 2
  have hΔ : 0 < Δ := half_pos (abs_pos.mpr hB)
  have hnear : Ω ∩ {y | Δ < |frameDet (shortField w X) B y|} ∈ 𝓝 z := by
    apply inter_mem (hΩ.mem_nhds hz)
    exact (((frameDet_contDiffOn
      (fun I => shortField_contDiffOn hΩ hX I) B).contDiffAt
      (hΩ.mem_nhds hz)).continuousAt.abs).preimage_mem_nhds
        (Ioi_mem_nhds (half_lt_self (abs_pos.mpr hB)))
  obtain ⟨d, hd, hpatch⟩ := Metric.mem_nhds_iff.mp hnear
  let R := d / 2
  have hR : 0 < R := half_pos hd
  have hp : closedBall z R ⊆ Ω ∩ {y | Δ < |frameDet (shortField w X) B y|} :=
    (closedBall_subset_ball (half_lt_self hd)).trans hpatch
  have hRΩ : closedBall z R ⊆ Ω := fun y hy => (hp hy).1
  obtain ⟨M, hM, hjets⟩ := G1.exists_uniform_coefficient_jet_bound hΩ
    (isCompact_closedBall z R) hRΩ X hX H
  exact ⟨R, Δ, M, hR, hΔ, hM, hRΩ,
    fun i j hj y hy => hjets i j hj y hy,
    fun y hy => ⟨B, (hp hy).2.le⟩⟩

end RothschildStein.G4
