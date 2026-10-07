-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.Kernel

@[expose] public section

noncomputable section

open Filter SchwartzMap TemperedDistribution
open scoped FourierTransform Topology

namespace Hormander.A

/-- Distributional convergence follows from convergence of the mollified Schwartz tests. -/
theorem Sδ_pairing_tendsto_of_Schwartz_tendsto {N : ℕ}
    (T : 𝓢'(Carrier N, ℂ)) (ψ : 𝓢(Carrier N, ℂ))
    (hψ : Tendsto (fun δ : ℝ => if hδ : 0 < δ then
        SδSchwartz N δ hδ ψ else ψ) (𝓝[>] (0 : ℝ)) (𝓝 ψ)) :
    Tendsto (fun δ : ℝ => if hδ : 0 < δ then
        Sδ N δ hδ T ψ else T ψ) (𝓝[>] (0 : ℝ)) (𝓝 (T ψ)) := by
  have hcont : Continuous (fun φ : 𝓢(Carrier N, ℂ) => T φ) := T.cont
  have h := hcont.continuousAt.tendsto.comp hψ
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := by simpa using hδ
  simp only [Function.comp_apply, dite_eq_left hδ', Sδ_apply]

end Hormander.A
