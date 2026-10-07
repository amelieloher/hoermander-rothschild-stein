-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactSourceRegularization

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RothschildStein.H3
variable {N : ℕ} {G : HomogeneousGroup N}

/-- An almost-everywhere bounded source has a compactly supported representative
with the same gauge support radius. -/
theorem exists_compact_source_representative (ν : G2.HomogeneousNorm G)
    {σ : ℝ} {p : ℝ≥0∞} {f : (Fin N → ℝ) → ℝ}
    (hf : MemLp f p volume) (hs : ∀ᵐ x, σ ≤ ν x → f x = 0) :
    ∃ g : (Fin N → ℝ) → ℝ, MemLp g p volume ∧ HasCompactSupport g ∧
      g =ᵐ[volume] f ∧ ∀ x, σ ≤ ν x → g x = 0 := by
  let A : Set (Fin N → ℝ) := {x | ν x < σ}
  have hA : IsOpen A := isOpen_lt ν.gauge.1 continuous_const
  let g := A.indicator f
  have heq : g =ᵐ[volume] f := by
    filter_upwards [hs] with x hx
    by_cases ha : x ∈ A
    · exact indicator_of_mem ha f
    · have hh : σ ≤ ν x := le_of_not_gt ha
      simp only [g, indicator_of_notMem ha f, hx hh]
  have hc : HasCompactSupport g := by
    apply (G2.isCompact_gauge_le ν.gauge σ).of_isClosed_subset isClosed_closure
    apply closure_minimal
    · intro x hx
      have ha : x ∈ A := by
        by_contra hn
        exact hx (indicator_of_notMem hn f)
      change ν x < σ at ha
      change ν x ≤ σ
      exact le_of_lt ha
    · exact isClosed_le ν.gauge.1 continuous_const
  refine ⟨g, hf.indicator hA.measurableSet, hc, heq, ?_⟩
  intro x hx
  have hn : x ∉ A := by
    change ¬ ν x < σ
    exact not_lt_of_ge hx
  exact indicator_of_notMem hn f

end RothschildStein.H3
