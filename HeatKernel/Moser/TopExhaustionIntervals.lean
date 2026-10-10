-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linarith

/-! # Exhausting open time intervals from below -/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace HeatKernel

/-- Terminal times approaching an open top endpoint strictly from below. -/
def interiorTopTime (b : ℝ) (n : ℕ) : ℝ := b - 1 / (n + 1 : ℝ)

/-- Every terminal time remains strictly below the top. -/
theorem interiorTopTime_lt (b : ℝ) (n : ℕ) : interiorTopTime b n < b := by
  have h : 0 < 1 / (n + 1 : ℝ) := by positivity
  dsimp [interiorTopTime]
  linarith

/-- Terminal times increase with the index. -/
theorem monotone_interiorTopTime (b : ℝ) : Monotone (interiorTopTime b) := by
  intro m n hmn
  have h : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
  dsimp [interiorTopTime]
  linarith

/-- Terminal times tend to the open top endpoint. -/
theorem tendsto_interiorTopTime (b : ℝ) : Tendsto (interiorTopTime b) atTop (𝓝 b) := by
  change Tendsto (fun n : ℕ => b - 1 / ((n : ℝ) + 1)) atTop (𝓝 b)
  simpa only [sub_zero] using
    tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The truncated time intervals cover the full open interval, including points arbitrarily near its top. -/
theorem iUnion_Ioo_interiorTopTime (a b : ℝ) :
    (⋃ n : ℕ, Ioo a (interiorTopTime b n)) = Ioo a b := by
  ext t
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact ⟨hn.1, hn.2.trans (interiorTopTime_lt b n)⟩
  · intro ht
    obtain ⟨n, hn⟩ := ((tendsto_interiorTopTime b).eventually (eventually_gt_nhds ht.2)).exists
    exact mem_iUnion.mpr ⟨n, ht.1, hn⟩

/-- The product cylinders with interior terminal times exhaust the open-top cylinder. -/
theorem iUnion_prod_Ioo_interiorTopTime {E : Type*} (a b : ℝ) (B : Set E) :
    (⋃ n : ℕ, (Ioo a (interiorTopTime b n)) ×ˢ B) = (Ioo a b) ×ˢ B := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp hz
    exact ⟨⟨hn.1.1, hn.1.2.trans (interiorTopTime_lt b n)⟩, hn.2⟩
  · intro hz
    have ht : z.1 ∈ ⋃ n : ℕ, Ioo a (interiorTopTime b n) := by
      rw [iUnion_Ioo_interiorTopTime]
      exact hz.1
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨n, hn, hz.2⟩

end HeatKernel
