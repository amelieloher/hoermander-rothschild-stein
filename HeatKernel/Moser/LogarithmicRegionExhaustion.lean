-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionLaterEstimates
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Passing logarithmic cylinder bounds to open time endpoints -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Uniform bounds on an increasing family of inner cylinders extend to the
open bottom time, even when the inner times are bounded above by a fixed time. -/
theorem measure_inter_prod_Ioo_le_of_interior_bottom_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure (ℝ × X))
    (start τ cap : ℝ) (hcap : start ≤ cap) (V : Set X) (T : Set (ℝ × X))
    (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      μ ((Ioo (min cap (start + 1 / (n + 1 : ℝ))) τ ×ˢ V) ∩ T) ≤ C) :
    μ ((Ioo start τ ×ˢ V) ∩ T) ≤ C := by
  let a := fun n : ℕ => min cap (start + 1 / (n + 1 : ℝ))
  have ha (n : ℕ) : start ≤ a n := le_min hcap (by
    have hpos : 0 ≤ (1 : ℝ) / (n + 1 : ℝ) := by positivity
    linarith)
  have hanti : Antitone a := by
    intro m n hmn
    apply min_le_min le_rfl
    have h := monotone_interiorTopTime 0 hmn
    dsimp [interiorTopTime] at h
    linarith
  have hmono : Monotone (fun n => (Ioo (a n) τ ×ˢ V) ∩ T) := by
    intro m n hmn z hz
    exact ⟨⟨⟨(hanti hmn).trans_lt hz.1.1.1, hz.1.1.2⟩, hz.1.2⟩, hz.2⟩
  have hu : (⋃ n : ℕ, (Ioo (a n) τ ×ˢ V) ∩ T) = (Ioo start τ ×ˢ V) ∩ T := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      exact ⟨⟨⟨(ha n).trans_lt hn.1.1.1, hn.1.1.2⟩, hn.1.2⟩, hn.2⟩
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz.1.1.1)
      have hleft : a n < z.1 := (min_le_right _ _).trans_lt (by linarith)
      exact mem_iUnion.mpr ⟨n, ⟨⟨hleft, hz.1.1.2⟩, hz.1.2⟩, hz.2⟩
  rw [← hu, hmono.measure_iUnion]
  exact iSup_le hbound

/-- Uniform inner-cylinder bounds also extend to the open top time when the
inner top times are bounded below by a fixed time. -/
theorem measure_inter_prod_Ioo_le_of_max_interior_top_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure (ℝ × X))
    (τ top floor : ℝ) (V : Set X) (T : Set (ℝ × X)) (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      μ ((Ioo τ (max floor (interiorTopTime top n)) ×ˢ V) ∩ T) ≤ C) :
    μ ((Ioo τ top ×ˢ V) ∩ T) ≤ C := by
  have H := measure_inter_prod_Ioo_le_of_interiorTopTime_bounds μ τ top
    (univ ×ˢ V) T (fun n =>
      (measure_mono (show T ∩ (univ ×ˢ V) ∩
        (Ioo τ (interiorTopTime top n) ×ˢ univ) ⊆
          (Ioo τ (max floor (interiorTopTime top n)) ×ˢ V) ∩ T from by
        intro z hz
        exact ⟨⟨⟨hz.2.1.1, hz.2.1.2.trans_le (le_max_right _ _)⟩, hz.1.2.2⟩, hz.1.1⟩)).trans
          (hbound n))
  convert H using 1
  congr 1
  ext z
  simp only [mem_inter_iff, mem_prod, mem_univ, true_and, and_true]
  tauto

end HeatKernel
