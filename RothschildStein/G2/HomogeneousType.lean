-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MeasureConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The punctured coordinate carrier has the same volume as the full
carrier for integration, because N is positive (BB Prop 3.21, pp. 105–106). -/
theorem volume_restrict_punctured (G : HomogeneousGroup N) :
    (volume : Measure (Fin N → ℝ)).restrict ({0}ᶜ) = volume := by
  have : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  exact restrict_compl_singleton 0

end RothschildStein.G2
