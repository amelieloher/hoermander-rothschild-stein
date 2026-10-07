-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RelcompactOpenExhaustion
public import RothschildStein.H3.WeakJetNormFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Local Sobolev membership supplies the locally integrable
function used by the literal distribution representation (BB p. 375). -/
theorem locallyIntegrableOn_of_memSobolevXLoc {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    {u : (Fin N → ℝ) → ℝ} (hu : memSobolevXLoc w X Ω k p u) :
    LocallyIntegrableOn u (Ω : Set (Fin N → ℝ)) volume := by
  obtain ⟨U,_,hU,hcover,_⟩ := exists_relcompact_open_exhaustion Ω
  intro x hx
  obtain ⟨j,hj⟩ := hcover x hx
  have hSob := hu (U j) (hU j).1 ((hU j).2.1.trans (hU (j+1)).2.2)
  have hh := locallyIntegrableOn_of_locallyIntegrable_restrict (hSob.1.locallyIntegrable hp)
  have hxint := hh x hj
  rw [(U j).isOpen.nhdsWithin_eq hj] at hxint
  exact hxint.filter_mono nhdsWithin_le_nhds

/-- The literal full Sobolev norm is finite, allowing
real-valued interior estimates to be restored to their ENNReal form. -/
theorem sobolevXENorm_lt_top_of_membership {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (k : ℕ) (p : ℝ≥0∞)
    {u : (Fin N → ℝ) → ℝ} (hu : memSobolevX w X Ω k p u) :
    sobolevXENorm w X Ω k p u < ⊤ := by
  unfold sobolevXENorm
  exact ENNReal.sum_lt_top.mpr (fun I hI => weakWordENorm_lt_top_of_memSobolev w X Ω k p u hu I hI)

end RothschildStein.H3
