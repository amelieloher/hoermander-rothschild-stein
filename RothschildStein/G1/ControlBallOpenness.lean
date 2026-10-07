-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CompactClosedControlBalls

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G1

/-- Under local control-distance comparison, ambient control balls are
open in the Euclidean space, including their domain restriction
(BB Thm 1.53, pp. 35–36). -/
theorem isOpen_rsBall_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (hs : 0 < s)
    (hcomparison : LocalControlComparison Ω w X s)
    {x : Fin n → ℝ} (hx : x ∈ Ω) (r : ℝ) :
    IsOpen (rsBall Ω w X x r) := by
  change IsOpen (Ω ∩ (controlDistance Ω w X x) ⁻¹' Iio (ENNReal.ofReal r))
  have hc := continuousOn_controlDistance_section_of_local_comparison hΩ w X hX hs hcomparison hx
  exact hc.isOpen_inter_preimage hΩ isOpen_Iio

end RothschildStein.G1
