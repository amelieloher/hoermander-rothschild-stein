-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupTaylorLp
public import RothschildStein.H3.FlowTaylor
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- The unit-step Lp interpolation estimate along a group
 flow. Its scalar Taylor identity is the sole flow-derivative input;
 spatial integrability and the remainder norm are proved. -/
theorem group_flow_unit_interpolation_of_taylor {n : ℕ} (G : HomogeneousGroup n)
    (E : ℝ → (Fin n → ℝ)) (hE : Measurable E)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u du ddu : (Fin n → ℝ) → ℝ}
    (hu : StronglyMeasurable u) (hup : MemLp u p volume)
    (hdd : StronglyMeasurable ddu) (hddp : MemLp ddu p volume)
    (ht : ∀ x, du x = u (G.mul x (E 1)) - u x -
      ∫ t in (0 : ℝ)..1, (1-t)*ddu (G.mul x (E t))) :
    MemLp du p volume ∧
      eLpNorm du p volume ≤ 2 * eLpNorm u p volume +
        ENNReal.ofReal (1/2 : ℝ) * eLpNorm ddu p volume := by
  let A : (Fin n → ℝ) → ℝ := fun x => u (G.mul x (E 1))
  let R : (Fin n → ℝ) → ℝ := fun x => ∫ t in (0 : ℝ)..1, (1-t)*ddu (G.mul x (E t))
  have hpres := RothschildStein.G2.measurePreserving_rightTranslation G (E 1)
  have ha : MemLp A p volume := hup.comp_measurePreserving hpres
  have han : eLpNorm A p volume = eLpNorm u p volume :=
    eLpNorm_comp_measurePreserving hu.aestronglyMeasurable hpres
  obtain ⟨hr,hrb⟩ := group_taylor_remainder_memLp_and_norm_le G E hE hp hpt hdd hddp
  have he : du = A - u - R := funext ht
  rw [he]
  refine ⟨(ha.sub hup).sub hr,?_⟩
  calc
    eLpNorm (A - u - R) p volume ≤ eLpNorm (A-u) p volume + eLpNorm R p volume :=
      eLpNorm_sub_le hp
    _ ≤ (eLpNorm A p volume + eLpNorm u p volume) +
        ENNReal.ofReal (1/2 : ℝ) * eLpNorm ddu p volume :=
      add_le_add (eLpNorm_sub_le hp) hrb
    _ = 2 * eLpNorm u p volume + ENNReal.ofReal (1/2 : ℝ) * eLpNorm ddu p volume := by
      rw [han,two_mul]

end RothschildStein.H3
