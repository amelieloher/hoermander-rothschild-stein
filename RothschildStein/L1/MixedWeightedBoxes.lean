-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxes
public import RothschildStein.P1.PaddingCoordinates

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- Restricting the radius restricts the actual weighted box;
no frame is selected again at the smaller radius. -/
theorem weightedBox_subset_of_radius_le {k : ℕ} (w : Fin k → ℕ+)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    G4.weightedBox w r ⊆ G4.weightedBox w R := by
  intro u hu i
  exact (hu i).trans_le (pow_le_pow_left₀ hr hrR _)

/-- Joining coordinates identifies a full weighted box with
the product of its two blocks, including empty blocks. -/
theorem joinPoint_mem_weightedBox_iff {n m : ℕ}
    (w : Fin n → ℕ+) (v : Fin m → ℕ+) (r : ℝ)
    (u : Fin n → ℝ) (z : Fin m → ℝ) :
    joinPoint u z ∈ G4.weightedBox (Fin.addCases w v) r ↔
      u ∈ G4.weightedBox w r ∧ z ∈ G4.weightedBox v r := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [joinPoint, Fin.addCases_left] using h (Fin.castAdd m i)
    · intro i
      simpa only [joinPoint, Fin.addCases_right] using h (Fin.natAdd n i)
  · rintro ⟨hu, hz⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [joinPoint, Fin.addCases_left] using hu j
    · intro j
      simpa only [joinPoint, Fin.addCases_right] using hz j

/-- A mixed box with separate coordinate and parameter radii
lies inside the lifted full box whenever both radii fit. -/
theorem joinPoint_mixed_weightedBox_subset {n m : ℕ}
    (w : Fin n → ℕ+) (v : Fin m → ℕ+)
    {a b c δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hac : a ≤ c) (hbc : b ≤ c) :
    (fun p : (Fin n → ℝ) × (Fin m → ℝ) => joinPoint p.1 p.2) ''
      (G4.weightedBox w (a * δ) ×ˢ G4.weightedBox v (b * δ)) ⊆
        G4.weightedBox (Fin.addCases w v) (c * δ) := by
  rintro _ ⟨⟨u, z⟩, ⟨hu, hz⟩, rfl⟩
  apply (joinPoint_mem_weightedBox_iff w v (c * δ) u z).mpr
  exact ⟨weightedBox_subset_of_radius_le w (mul_nonneg ha hδ)
      (mul_le_mul_of_nonneg_right hac hδ) hu,
    weightedBox_subset_of_radius_le v (mul_nonneg hb hδ)
      (mul_le_mul_of_nonneg_right hbc hδ) hz⟩

/-- A smaller full lifted box fits inside the mixed chart box.
This is the containment needed before the lifted rescaling argument. -/
theorem full_weightedBox_subset_mixed {n m : ℕ}
    (w : Fin n → ℕ+) (v : Fin m → ℕ+)
    {a b c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hca : c ≤ a) (hcb : c ≤ b) :
    (P1.paddingCoordinates n m) '' G4.weightedBox (Fin.addCases w v) (c * δ) ⊆
      G4.weightedBox w (a * δ) ×ˢ G4.weightedBox v (b * δ) := by
  rintro _ ⟨ξ, hξ, rfl⟩
  have he : ξ = joinPoint (P1.paddingBaseCLM n m ξ) (P1.paddingFiberCLM n m ξ) := by
    symm
    simpa only [P1.paddingJoinCLM_apply] using P1.paddingJoinCLM_projections n m ξ
  rw [he] at hξ
  obtain ⟨hu, hz⟩ := (joinPoint_mem_weightedBox_iff w v (c * δ) _ _).mp hξ
  exact ⟨weightedBox_subset_of_radius_le w (mul_nonneg hc hδ)
      (mul_le_mul_of_nonneg_right hca hδ) hu,
    weightedBox_subset_of_radius_le v (mul_nonneg hc hδ)
      (mul_le_mul_of_nonneg_right hcb hδ) hz⟩

end RothschildStein.L1
