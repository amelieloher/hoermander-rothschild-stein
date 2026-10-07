-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ConstantControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology

namespace RothschildStein.G4

/-- A weighted coefficient box with strict coordinate bounds. -/
def weightedBox {m : ℕ} (w : Fin m → ℕ+) (r : ℝ) : Set (Fin m → ℝ) :=
  {a | ∀ i, |a i| < r ^ (w i : ℕ)}

/-- Weighted boxes are Euclidean-open (BB Remark 9.10, p. 404). -/
theorem isOpen_weightedBox {m : ℕ} (w : Fin m → ℕ+) (r : ℝ) :
    IsOpen (weightedBox w r) := by
  have heq : weightedBox w r = ⋂ i : Fin m, {a : Fin m → ℝ | |a i| < r ^ (w i : ℕ)} := by
    ext a
    simp [weightedBox]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt ((continuous_apply i).abs) continuous_const)

/-- Finitely many strict weighted bounds have one common smaller
positive cost; no coordinate-dependent radius is retained
(BB Remark 9.10, p. 404). -/
theorem exists_smaller_weighted_cost {m : ℕ} (w : Fin m → ℕ+)
    {a : Fin m → ℝ} {r : ℝ} (hr : 0 < r) (ha : a ∈ weightedBox w r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧ ∀ i, |a i| ≤ δ ^ (w i : ℕ) := by
  let U : Set ℝ := ⋂ i : Fin m, {δ : ℝ | |a i| < δ ^ (w i : ℕ)}
  have hU : IsOpen U := isOpen_iInter_of_finite
    (fun i => isOpen_lt continuous_const (continuous_id.pow (w i : ℕ)))
  have hrU : r ∈ U := by simpa only [U, mem_iInter, mem_ofPred_eq, weightedBox] using ha
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hrU)
  let d := min r ε / 2
  have hd : 0 < d := half_pos (lt_min hr hε)
  have hdr : d < r := (half_lt_self (lt_min hr hε)).trans_le (min_le_left _ _)
  have hdε : d < ε := (half_lt_self (lt_min hr hε)).trans_le (min_le_right _ _)
  have hmem : r - d ∈ U := hεU (by
    rw [mem_ball, Real.dist_eq]
    simpa only [sub_sub_cancel_left, abs_neg, abs_of_pos hd] using hdε)
  refine ⟨r - d, by linarith, by linarith, ?_⟩
  intro i
  exact ((mem_iInter.mp hmem) i).le

end RothschildStein.G4
