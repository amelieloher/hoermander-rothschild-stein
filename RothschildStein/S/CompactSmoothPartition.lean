-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Locality
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators Manifold
namespace RothschildStein.S
variable {n m : ℕ}

/-- Every finite open cover of a compact set has a compact
smooth partition supported strictly inside the prescribed sets. Multiplying
Mathlib's subordinate partition by one compact plateau makes every support
compact (BB (2.23), p. 85; partition existence). -/
theorem exists_compact_smooth_finite_partition
    (K : Compacts (Fin n → ℝ)) (U : Fin m → Set (Fin n → ℝ))
    (hU : ∀ i,IsOpen (U i)) (hcover : (K : Set (Fin n → ℝ)) ⊆ ⋃ i,U i) :
    ∃ ζ : Fin m → (Fin n → ℝ) → ℝ,
      (∀ i,ContDiff ℝ (⊤ : ℕ∞) (ζ i) ∧ HasCompactSupport (ζ i) ∧ tsupport (ζ i) ⊆ U i) ∧
      ∀ x ∈ (K : Set (Fin n → ℝ)),∑ i,ζ i x = 1 := by
  let W : Opens (Fin n → ℝ) := ⟨⋃ i,U i,isOpen_iUnion hU⟩
  obtain ⟨χ,V,_hV,hKV,_hVW,hone⟩ := exists_test_plateau W K hcover
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ,Fin n → ℝ)) K.isCompact.isClosed U hU hcover
  refine ⟨fun i x => χ x*ρ i x,?_,?_⟩
  · intro i
    refine ⟨χ.contDiff.mul (ρ i).contMDiff.contDiff,?_,?_⟩
    · exact χ.hasCompactSupport.mul_right
    · exact tsupport_mul_subset_right.trans (hρ i)
  · intro x hx
    have hχ : χ x = (1 : ℝ) := hone (hKV hx)
    have hs : ∑ i,ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    rw [← Finset.mul_sum,hχ,one_mul,hs]

end RothschildStein.S
