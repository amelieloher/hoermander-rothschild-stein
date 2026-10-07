-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {N : ℕ} {F : KernelFrame N} {m : ℕ}

/-- Every row and column of a regular component is absolutely integrable,
including endpoints outside the cutoff region. -/
theorem IsRegularKernel.integrable_slices
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F m r)
    (ξ : Fin N → ℝ) : Integrable (r ξ) ∧ Integrable (fun η => r η ξ) := by
  have hc := hr.1.continuous
  have hrow : HasCompactSupport (r ξ) := by
    apply (hr.2.1.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (hr.2.1.image continuous_snd).isClosed
    intro η hη
    exact ⟨(ξ, η), subset_tsupport _ hη, rfl⟩
  have hcolumn : HasCompactSupport (fun η => r η ξ) := by
    apply (hr.2.1.image continuous_fst).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (hr.2.1.image continuous_fst).isClosed
    intro η hη
    exact ⟨(η, ξ), subset_tsupport _ hη, rfl⟩
  exact ⟨(hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hrow,
    (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hcolumn⟩

end RothschildStein.P1
