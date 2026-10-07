-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A common coordinate speed bound on separate open inverse
neighborhoods gives the same bound across a whole closed interval.
A finite subordinate partition glues the estimates without multiplying
the constant by the number of neighborhoods (BB Prop 9.52, p. 449). -/
theorem coordinate_variation_of_local_bound {a b C : ℝ} (hab : a ≤ b)
    (f : ℝ → ℝ)
    (hlocal : ∀ t ∈ Icc a b, ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∀ u ∈ Icc a b ∩ V, ∀ v ∈ Icc a b ∩ V,
        |f v - f u| ≤ C * |v - u|) :
    |f b - f a| ≤ C * (b - a) := by
  classical
  choose V hV hmem hbound using fun t : Icc a b => hlocal t t.property
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hpart⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab
      (fun j => (hV j).preimage continuous_subtype_val)
      (fun j _ => mem_iUnion.mpr ⟨j, hmem j⟩)
  have hstep (j : ℕ) :
      |f (t (j + 1)) - f (t j)| ≤ C * ((t (j + 1) : ℝ) - t j) := by
    obtain ⟨k, hk⟩ := hpart j
    have hleft : (t j : ℝ) ∈ V k := hk ⟨le_rfl, hmono j.le_succ⟩
    have hright : (t (j + 1) : ℝ) ∈ V k := hk ⟨hmono j.le_succ, le_rfl⟩
    have hle : (t j : ℝ) ≤ t (j + 1) := hmono j.le_succ
    simpa only [abs_of_nonneg (sub_nonneg.mpr hle)] using
      hbound k (t j) ⟨(t j).property, hleft⟩
        (t (j + 1)) ⟨(t (j + 1)).property, hright⟩
  have hwhole : ∀ j, |f (t j) - f a| ≤ C * ((t j : ℝ) - a) := by
    intro j
    induction j with
    | zero => simp only [ht0, sub_self, abs_zero, mul_zero, le_refl]
    | succ j hj =>
      have hsplit : f (t (j + 1)) - f a =
          (f (t (j + 1)) - f (t j)) + (f (t j) - f a) := by ring
      rw [hsplit]
      exact (abs_add_le _ _).trans ((add_le_add (hstep j) hj).trans_eq (by ring))
  simpa only [hN N le_rfl] using hwhole N

end RothschildStein.G4
