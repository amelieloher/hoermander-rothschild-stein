-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.DualTimeBalance

/-! # Compatible representatives of dual energy pairings -/

@[expose] public section
open Set MeasureTheory
namespace HeatKernel

/-- Square-integrable dual representatives of specified value and flux pairings,
 together with their Bochner weak time balance. -/
def IsDualEnergyPair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Set ℝ) (value flux : ℝ → E → ℝ) (D F : ℝ → (E →L[ℝ] ℝ)) : Prop :=
  MemLp D 2 (volume.restrict J) ∧ MemLp F 2 (volume.restrict J) ∧
    (∀ᵐ t ∂volume.restrict J, ∀ v, D t v = value t v) ∧
    (∀ᵐ t ∂volume.restrict J, ∀ v, F t v = flux t v) ∧
    SatisfiesDualTimeBalance J D F

end HeatKernel
