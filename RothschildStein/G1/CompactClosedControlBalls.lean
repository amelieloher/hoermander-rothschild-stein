-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlEuclideanContinuity
public import RothschildStein.Definitions.rsBall

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G1

/-- Each actual ambient distance
section is Euclidean-continuous on the domain
(BB Thm 1.53, pp. 35–36). -/
theorem continuousOn_controlDistance_section_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (hs : 0 < s)
    (hcomparison : LocalControlComparison Ω w X s) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    ContinuousOn (controlDistance Ω w X x) Ω := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (continuous_controlDistance_of_local_comparison hΩ w X hX hs hcomparison).comp
    ((continuous_const : Continuous (fun _ : Ω => (⟨x,hx⟩ : Ω))).prodMk continuous_id)

end RothschildStein.G1
