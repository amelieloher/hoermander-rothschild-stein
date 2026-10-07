-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalConvolutionBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
open G2

/-- Compactly supported Lp data convolved with a positive-type
kernel give a globally defined locally integrable function. No global
Lp membership of the convolution is required. -/
theorem PositiveType.locallyIntegrable_convolution {n : ℕ} {G : HomogeneousGroup n}
    {α : ℝ} {T f : (Fin n → ℝ) → ℝ} (hT : PositiveType G α T)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ : ℝ} (hρ : 0 < ρ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume)
    (hsupp : ∀ᵐ y ∂volume, ρ ≤ ν y → f y = 0) :
    LocallyIntegrable (groupConvolution G f T) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn ν.gauge.1.continuousOn
  let R := max C 0+1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hKR : K ⊆ {x | ν x < R} := by
    intro x hx
    have hb := hC x hx
    have hn : ν x ≤ |ν x| := le_abs_self _
    have hm : C ≤ max C 0 := le_max_left _ _
    change ν x < max C 0+1
    rw [Real.norm_eq_abs] at hb
    linarith
  have hl := (hT.local_convolution_bound ν h1 hsym hρ hR hp hf hsupp).1.locallyIntegrable hp
  have hi := hl.integrableOn_isCompact hK
  simpa only [IntegrableOn, Measure.restrict_restrict_of_subset hKR] using hi

end RothschildStein.H3
