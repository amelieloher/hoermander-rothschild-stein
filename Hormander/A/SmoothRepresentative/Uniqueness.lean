-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Fourier
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.A

/-- Two `L¹` functions defining the same tempered
distribution are equal in `L¹`; in particular all Fourier representatives of a fixed tempered
distribution obtained at different Sobolev orders agree almost everywhere. -/
theorem lp_eq_of_toTemperedDistribution_eq {N : ℕ} {v w : Lp ℂ 1 (volume : Measure (Carrier N))}
    (h : (v : 𝓢'(Carrier N, ℂ)) = (w : 𝓢'(Carrier N, ℂ))) : v = w := by
  have hker := Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure (Carrier N)))
    (p := 1)
  have : v - w ∈ (Lp.toTemperedDistributionCLM ℂ (volume : Measure (Carrier N)) 1).ker := by
    rw [LinearMap.mem_ker]
    rw [map_sub]
    simpa [Lp.toTemperedDistributionCLM_apply, sub_eq_zero] using h
  rw [hker] at this
  exact sub_eq_zero.mp this

end Hormander.A
