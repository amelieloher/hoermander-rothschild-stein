-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformFiniteLieJetFlow
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- The open spatial buffer around a set of centres. -/
def centreBuffer {N : ℕ} (K : Set (Fin N → ℝ)) (r : ℝ) : Opens (Fin N → ℝ) :=
  ⟨⋃ x ∈ K, ball x r, isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball))⟩

theorem mem_centreBuffer_iff {N : ℕ} {K : Set (Fin N → ℝ)} {r : ℝ}
    {y : Fin N → ℝ} : y ∈ centreBuffer K r ↔ ∃ x ∈ K, y ∈ ball x r := by
  simp only [centreBuffer, Opens.mem_mk, mem_iUnion, exists_prop]

/-- Fixed half-buffers have a numerical closed-ball margin in the full
coefficient/spatial cylinder, uniformly over all centres. -/
theorem closedBall_subset_coefficient_centreBuffer {m N : ℕ}
    (K : Set (Fin N → ℝ)) {r : ℝ} (hr : 0 < r)
    {q : (Fin m → ℝ) × (Fin N → ℝ)}
    (hq : q ∈ ball 0 (1/2 : ℝ) ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) :
    closedBall q (min (1/4 : ℝ) (r/4)) ⊆
      ball 0 (1 : ℝ) ×ˢ (centreBuffer K r : Set (Fin N → ℝ)) := by
  intro y hy
  obtain ⟨x,hx,hqx⟩ := mem_centreBuffer_iff.mp hq.2
  have hdist : dist y q ≤ min (1/4 : ℝ) (r/4) := mem_closedBall.mp hy
  have hfst : dist y.1 q.1 ≤ min (1/4 : ℝ) (r/4) :=
    (show dist y.1 q.1 ≤ dist y q from by
      simpa only [dist_eq_norm, Prod.fst_sub] using norm_fst_le (y-q)).trans hdist
  have hsnd : dist y.2 q.2 ≤ min (1/4 : ℝ) (r/4) :=
    (show dist y.2 q.2 ≤ dist y q from by
      simpa only [dist_eq_norm, Prod.snd_sub] using norm_snd_le (y-q)).trans hdist
  refine ⟨?_,mem_centreBuffer_iff.mpr ⟨x,hx,?_⟩⟩
  · rw [mem_ball]
    have ht := dist_triangle y.1 q.1 0
    have hc := mem_ball.mp hq.1
    have hm := min_le_left (1/4 : ℝ) (r/4)
    linarith
  · rw [mem_ball]
    have ht := dist_triangle y.2 q.2 x
    have hc := mem_ball.mp hqx
    have hm := min_le_right (1/4 : ℝ) (r/4)
    linarith
end RothschildStein.G3
