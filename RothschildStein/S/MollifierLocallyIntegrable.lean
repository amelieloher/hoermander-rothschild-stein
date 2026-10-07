-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.S
variable {n : ℕ}

/-- Local integrability suffices for smooth mollification; no global
Lp assumption is needed (BB Lemma 2.8, pp. 72–73). -/
theorem contDiff_euclideanRegularize_of_locallyIntegrable (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanRegularize n f ε) := by
  rw [← additiveRegularize_eq hn]
  exact RothschildStein.G2.contDiff_groupConvolution_left
    (additiveCoordinateGroup hn)
    (RothschildStein.G2.contDiff_groupMollifierScale _ _ ε)
    (RothschildStein.G2.hasCompactSupport_groupMollifierScale _ _ hε) hf

/-- Compact locally integrable data yield compact smooth
regularizations (BB Lemma 2.8, pp. 72–73). -/
theorem euclideanRegularize_smooth_compact_of_locallyIntegrable (hn : 0 < n)
    {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hcf : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanRegularize n f ε) ∧
      HasCompactSupport (euclideanRegularize n f ε) := by
  refine ⟨contDiff_euclideanRegularize_of_locallyIntegrable hn hf hε,?_⟩
  rw [← additiveRegularize_eq hn]
  exact RothschildStein.G2.hasCompactSupport_groupRegularize _ _ hε hcf

end RothschildStein.S
