-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedPoleDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.P1

variable {N : ℕ}

/-- The weighted decay criterion also applies to normed targets, including
the continuous linear maps that occur as successive derivative fields. -/
theorem hasFDerivAt_zero_of_weighted_norm_decay {P B : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (G : HomogeneousGroup N) (W q : ℕ) (hW : ∀ j, G.weight j ≤ W) (hq : 0 < q)
    (H : P × (Fin N → ℝ) → B) (K : Set P) (p : P) (hK : K ∈ 𝓝 p)
    (hzero : ∀ a ∈ K, H (a, 0) = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a ∈ K, ∀ u : Fin N → ℝ, kgauge G u ≤ 1 →
      ‖H (a, u)‖ ≤ C * kgauge G u ^ (W + q)) :
    HasFDerivAt H (0 : (P × (Fin N → ℝ)) →L[ℝ] B) (p, 0) := by
  have hp := hzero p (mem_of_mem_nhds hK)
  have hs := hasFDerivAt_zero_of_weighted_decay G W q hW hq
    (fun z => ‖H z‖) K p hK
    (fun a ha => by simp only [hzero a ha, norm_zero]) C hC
    (fun a ha u hu => by simpa only [abs_norm] using hbound a ha u hu)
  rw [hasFDerivAt_iff_tendsto] at hs ⊢
  simpa only [hp, norm_zero, sub_zero, zero_apply, norm_norm] using hs

end RothschildStein.P1
