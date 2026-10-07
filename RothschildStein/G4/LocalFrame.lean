-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameBounds
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- A nondegenerate point has a compact original-domain frame
buffer and bounded linear coordinate functionals. This is a local bound;
suboptimal scale estimates are provided by the separate weighted calculus
(BB Proposition 9.29, pp. 421–422). -/
theorem exists_local_frame_bound {ι : Type*} {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (Z J) Ω)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ Ω)
    (hspan : ∃ B : Fin n → ι, frameDet Z B x₀ ≠ 0) :
    ∃ B : Fin n → ι, ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧
      closedBall x₀ R ⊆ Ω ∧ (∀ y ∈ closedBall x₀ R, frameDet Z B y ≠ 0) ∧
      ∀ y ∈ closedBall x₀ R, ∀ i (v : Fin n → ℝ),
        |frameCoefficient Z B (fun _ => v) i y| ≤ C * ‖v‖ := by
  obtain ⟨B, hB⟩ := hspan
  have hnear : Ω ∩ {y | frameDet Z B y ≠ 0} ∈ 𝓝 x₀ := by
    apply inter_mem (hΩ.mem_nhds hx₀)
    exact ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds hx₀)).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hB)
  obtain ⟨d, hd, hdpatch⟩ := Metric.mem_nhds_iff.mp hnear
  let R := d / 2
  have hR : 0 < R := half_pos hd
  have hpatch : closedBall x₀ R ⊆ Ω ∩ {y | frameDet Z B y ≠ 0} :=
    (closedBall_subset_ball (half_lt_self hd)).trans hdpatch
  obtain ⟨M, hM, hcoord⟩ := exists_compact_frame_coordinate_bound hZ B
    (isCompact_closedBall x₀ R) (fun y hy => (hpatch hy).1) (fun y hy => (hpatch hy).2)
  let C := n * M + 1
  have hnM : 0 ≤ (n : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM.le
  refine ⟨B, R, hR, C, by dsimp [C]; linarith, fun y hy => (hpatch hy).1,
    fun y hy => (hpatch hy).2, ?_⟩
  intro y hy i v
  exact (frameCoefficient_le_of_coordinate_bounds Z B (fun _ => v) i y
    (fun k => hcoord i k y hy)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))

end RothschildStein.G4
