-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalFundamentalFromRepresentation
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Extend the punctured integrable representative by
zero outside the local domain. The value at zero is irrelevant because
Lebesgue measure has no atom there (BB pp. 251–253). -/
theorem integrable_zeroExtension_of_punctured (G : HomogeneousGroup N) (Ω : TopologicalSpace.Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ} (hγ : IntegrableOn γ ((Ω : Set (Fin N → ℝ)) \ {0})) :
    Integrable ((Ω : Set (Fin N → ℝ)).indicator γ) := by
  have finNonempty : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  have hi : IntegrableOn γ (Ω : Set (Fin N → ℝ)) := by
    apply hγ.mono_set_ae
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
    intro hxΩ
    exact ⟨hxΩ, hx⟩
  exact hi.integrable_indicator Ω.isOpen.measurableSet

end RothschildStein.H1
