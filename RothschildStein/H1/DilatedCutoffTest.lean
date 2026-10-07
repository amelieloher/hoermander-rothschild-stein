-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.TransposeHomogeneity
public import RothschildStein.H1.SmoothShellCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 2: positive dilation preserves the compact support
of a smooth cutoff. -/
theorem hasCompactSupport_comp_dilate {θ : (Fin N → ℝ) → ℝ}
    (hs : HasCompactSupport θ) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (θ ∘ G.dilate t) :=
  hs.comp_homeomorph (G2.dilationHomeomorph G t ht)

/-- A gauge cutoff equal to one on a positive inner ball is
one on a neighborhood of the origin. -/
theorem gaugeCutoff_eventually_one {ν θ : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {a : ℝ} (ha : 0 < a)
    (he : ∀ x, ν x ≤ a → θ x = 1) :
    θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1 := by
  have hν0 : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have hn : ∀ᶠ x in 𝓝 (0 : Fin N → ℝ), ν x < a :=
    hν.1.continuousAt.eventually (gt_mem_nhds (by simpa only [hν0] using ha))
  exact hn.mono fun x hx => he x hx.le

/-- Dilation preserves equality to one near the origin. -/
theorem cutoff_comp_dilate_eventually_one {θ : (Fin N → ℝ) → ℝ}
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) (t : ℝ) :
    (θ ∘ G.dilate t) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1 := by
  have ht : Tendsto (G.dilate t) (𝓝 (0 : Fin N → ℝ)) (𝓝 (0 : Fin N → ℝ)) := by
    have hc : ContinuousAt (G.dilate t) (0 : Fin N → ℝ) := (G2.continuous_dilate G t).continuousAt
    simpa only [G2.dilate_zero] using hc.tendsto
  exact he.comp_tendsto ht

/-- Step 2: a difference of two dilated compact cutoffs is
an actual smooth test on the punctured carrier. -/
theorem exists_dilatedCutoffDifference_test {θ : (Fin N → ℝ) → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hs : HasCompactSupport θ)
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) :
    ∃ ψ : TestFunction ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩ ℝ (⊤ : ℕ∞),
      ∀ x, ψ x = θ (G.dilate s x) - θ (G.dilate t x) := by
  let F := fun x => θ (G.dilate s x) - θ (G.dilate t x)
  have hz : F =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
    filter_upwards [cutoff_comp_dilate_eventually_one G he s,
      cutoff_comp_dilate_eventually_one G he t] with x hxs hxt
    change θ (G.dilate s x) - θ (G.dilate t x) = 0
    change θ (G.dilate s x) = 1 at hxs
    change θ (G.dilate t x) = 1 at hxt
    rw [hxs, hxt, sub_self]
  have h0 : (0 : Fin N → ℝ) ∉ tsupport F := notMem_tsupport_iff_eventuallyEq.mpr hz
  refine ⟨⟨F, ((hθ.comp (G2.contDiff_dilate G s)).sub (hθ.comp (G2.contDiff_dilate G t))),
    (hasCompactSupport_comp_dilate G hs hs0).sub (hasCompactSupport_comp_dilate G hs ht0), ?_⟩, fun _ => rfl⟩
  intro x hx
  change x ∈ ({0}ᶜ : Set (Fin N → ℝ))
  simp only [mem_compl_iff, mem_singleton_iff]
  intro heq
  exact h0 (heq ▸ hx)

end RothschildStein.H1
