-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LpExhaustion
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- Uniform gauge-sublevel estimates imply a global Lp bound, without
requiring the gauge to define a metric. -/
theorem memLp_of_uniform_sublevel_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν f : X → ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) {C : ℝ≥0∞} (hC : C < ∞)
    (hb : ∀ n : ℕ, eLpNorm f p (μ.restrict {x | ν x < (n : ℝ) + 1}) ≤ C) :
    MemLp f p μ ∧ eLpNorm f p μ ≤ C := by
  let s : ℕ → Set X := fun n => {x | ν x < (n : ℝ) + 1}
  have hd : Directed (· ⊆ ·) s := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro x hx
      have hh : (i : ℝ) ≤ (max i j : ℕ) := by exact_mod_cast le_max_left i j
      change ν x < (max i j : ℕ) + 1
      change ν x < (i : ℝ) + 1 at hx
      linarith
    · intro x hx
      have hh : (j : ℝ) ≤ (max i j : ℕ) := by exact_mod_cast le_max_right i j
      change ν x < (max i j : ℕ) + 1
      change ν x < (j : ℝ) + 1 at hx
      linarith
  have hu : (⋃ n, s n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (ν x)
    exact mem_iUnion.mpr ⟨n, by change ν x < (n : ℝ) + 1; linarith⟩
  have he := eLpNorm_iUnion_of_directed μ f hp0 hpt s hd
    (by simpa only [hu, Measure.restrict_univ] using hf)
  simp only [hu, Measure.restrict_univ] at he
  have hn : eLpNorm f p μ ≤ C := he.trans_le (iSup_le hb)
  exact ⟨hn.trans_lt hC, hn⟩

end RothschildStein.H3
