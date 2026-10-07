-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)
open Set

/-- The finite tail vanishes below unit gauge radius. -/
theorem typeZeroUnitTail_eq_zero_of_lt_one (ν k : (Fin N → ℝ) → ℝ)
    {w : Fin N → ℝ} (hw : ν w < 1) : typeZeroUnitTail ν k w = 0 := by
  apply indicator_of_notMem
  intro h
  exact (not_le_of_gt hw) h.1

/-- On the unit ball a unit-supported source splits the kernel exactly into
its radial truncation and the finite annular tail, including the diagonal. -/
theorem unit_source_kernel_split (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (k u : (Fin N → ℝ) → ℝ)
    (hsu : ∀ y, 1 ≤ ν y → u y = 0) {x : Fin N → ℝ} (hx : ν x < 1)
    (y : Fin N → ℝ) :
    u y * k (G.mul (G.inv y) x) =
      u y * truncatedKernel G ν k x y +
      u y * typeZeroUnitTail ν k (G.mul (G.inv y) x) := by
  by_cases hy : u y = 0
  · simp only [hy, zero_mul, zero_add]
  have hny : ν y < 1 := lt_of_not_ge (fun h => hy (hsu y h))
  have hw : ν (G.mul (G.inv y) x) < 2 := by
    have hm := ν.mul_le (G.inv y) x
    rw [h1, one_mul, hsym y] at hm
    linarith
  by_cases hn : ν (G.mul (G.inv y) x) < 1
  · rw [typeZeroUnitTail_eq_zero_of_lt_one ν k hn]
    unfold truncatedKernel G2.gaugeDistance
    rw [radialCutoff_eq_one hn.le]
    ring
  · have hm : G.mul (G.inv y) x ∈ {w | 1 ≤ ν w ∧ ν w ≤ 2} :=
      ⟨le_of_not_gt hn, hw.le⟩
    rw [typeZeroUnitTail, indicator_of_mem hm]
    unfold truncatedKernel G2.gaugeDistance
    ring

end RothschildStein.H3
