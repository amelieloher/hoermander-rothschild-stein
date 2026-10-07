-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory

/-- Joint measurability of homogeneous group multiplication. -/
theorem group_mul_measurable {n : ℕ} (G : HomogeneousGroup n) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → ℝ) => G.mul z.1 z.2) :=
  (RothschildStein.G2.continuous_mul G).measurable

/-- A measurable parameter family of right translations is jointly measurable. -/
theorem group_right_transport_measurable {α : Type*} [MeasurableSpace α]
    {n : ℕ} (G : HomogeneousGroup n) {E : α → (Fin n → ℝ)} (hE : Measurable E) :
    Measurable (fun z : α × (Fin n → ℝ) => G.mul z.2 (E z.1)) := by
  have hpair : Measurable (fun z : α × (Fin n → ℝ) => (z.2,E z.1)) :=
    measurable_snd.prodMk (hE.comp measurable_fst)
  simpa only [Function.comp_def] using (group_mul_measurable G).comp hpair

end RothschildStein.H3
