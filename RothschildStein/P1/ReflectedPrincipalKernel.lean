-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.DifferentialReflection
public import RothschildStein.H1.DifferentialLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

/-- Reflection exchanges the two fundamental-kernel poles.
Only their off-zero equality is required, so arbitrary assignments at
zero cannot affect the transformed principal kernel (BB p. 546). -/
theorem differentialReflection_kernelSwap {N : ℕ} (P : SmoothDifferentialOperator N)
    {Γ Γstar : (Fin N → ℝ) → ℝ}
    (hstar : ∀ u, u ≠ 0 → Γstar u = Γ (-u))
    (hreg : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) Γstar {(0 : Fin N → ℝ)}ᶜ)
    {u : Fin N → ℝ} (hu : u ≠ 0) :
    (differentialReflection P).apply Γstar u = P.apply Γ (-u) := by
  have hu' : -u ≠ 0 := neg_ne_zero.mpr hu
  have he : (fun y => Γstar (-y)) =ᶠ[𝓝 (-u)] Γ := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (show -u ∈ {(0 : Fin N → ℝ)}ᶜ by simpa using hu')] with y hy
    rw [hstar (-y) (by simpa using hy), neg_neg]
  have h := differentialReflection_apply P hreg hu'
  rw [neg_neg] at h
  exact h.trans (H1.differentialOperator_germ_eq P he)

end RothschildStein.P1
