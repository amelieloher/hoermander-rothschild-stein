-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PositiveType

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The order-zero kernel seminorm is the actual unit-sphere maximum
Λ_{T,0} (BB Definition 8.13 and (8.7), p. 346). -/
def kernelSphereBound (ν T : (Fin N → ℝ) → ℝ) : ℝ :=
  sSup ((fun x => |T x|) '' {x | ν x = 1})

/-- The maximum defining Λ_{T,0} is attained, nonnegative, and gives
precisely the homogeneous pointwise bound in BB (8.7). -/
theorem PositiveType.kernelSphereBound_properties {α : ℝ}
    {T ν : (Fin N → ℝ) → ℝ} (hT : PositiveType G α T) (hν : G.IsHomogeneousGauge ν) :
    0 ≤ kernelSphereBound ν T ∧
    (∃ z, ν z = 1 ∧ |T z| = kernelSphereBound ν T) ∧
    ∀ x, x ≠ 0 → |T x| ≤ kernelSphereBound ν T *
      (ν x) ^ (α - (G.homogeneousDimension : ℝ)) := by
  obtain ⟨M, hM, ⟨z, hz, hzM⟩, hb, hglobal⟩ := hT.sphere_bound hν
  have hg : IsGreatest ((fun x => |T x|) '' {x | ν x = 1}) M := by
    refine ⟨⟨z, hz, hzM⟩, ?_⟩
    rintro b ⟨x, hx, rfl⟩
    exact hb x hx
  have he : kernelSphereBound ν T = M := hg.isLUB.csSup_eq ⟨M, hg.1⟩
  rw [he]
  exact ⟨hM, ⟨z, hz, hzM⟩, hglobal⟩

end RothschildStein.H3
