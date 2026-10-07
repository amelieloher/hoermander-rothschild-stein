-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The translated compact test has a common compact
integration-variable support on each parameter ball. This reuses the
convolution support lemma (BB Prop 6.29, p. 277). -/
theorem exists_commonTranslatedSupport {ψ : (Fin N → ℝ) → ℝ}
    (hs : HasCompactSupport ψ) (x₀ : Fin N → ℝ) :
    ∃ K : Set (Fin N → ℝ), IsCompact K ∧ ∀ x ∈ ball x₀ 1,
      ∀ w ∉ K, ψ (G.mul x (G.inv w)) = 0 := by
  let K := (fun u : Fin N → ℝ => -u) '' G2.groupKernelSupport G ψ x₀
  refine ⟨K, (G2.isCompact_groupKernelSupport G hs x₀).image continuous_neg, ?_⟩
  intro x hx w hw
  have hu : -w ∉ G2.groupKernelSupport G ψ x₀ := by
    intro hu
    exact hw ⟨-w, hu, neg_neg w⟩
  have he := G2.groupKernel_vanish G hx hu
  simpa only [G2.groupKernel, neg_neg] using he

/-- A translated compact test has compact support for
every fixed base point. -/
theorem hasCompactSupport_leftInv_translate {ψ : (Fin N → ℝ) → ℝ}
    (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    HasCompactSupport (fun w => ψ (G.mul x (G.inv w))) := by
  obtain ⟨K, hK, he⟩ := exists_commonTranslatedSupport G hs x
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro w hw
  by_contra hn
  exact hw (he x (by simp) w hn)

end RothschildStein.H1
