-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalKernelMeasurable

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A C^budget model remainder becomes the actual
regular kernel after chart composition and compact endpoint cutoffs. No
regularity of the chart outside its coordinate domain is required. -/
theorem LiftedChart.isRegularKernel_cutoff_model
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (budget : ℕ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (R : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ)
    (hR : ContDiff ℝ budget R) :
    IsRegularKernel F budget (fun ξ η => a ξ * b η * R (ξ, η, F.Θ η ξ)) := by
  let κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ :=
    fun ξ η => a ξ * b η * R (ξ, η, F.Θ η ξ)
  have hs : Function.support (Function.uncurry κ) ⊆ tsupport a ×ˢ tsupport b := by
    intro p hp
    constructor
    · apply subset_tsupport a
      intro hz
      exact hp (by simp only [Function.uncurry, κ, hz, zero_mul])
    · apply subset_tsupport b
      intro hz
      exact hp (by simp only [Function.uncurry, κ, hz, mul_zero, zero_mul])
  have ht : tsupport (Function.uncurry κ) ⊆ tsupport a ×ˢ tsupport b :=
    closure_minimal hs ((isClosed_tsupport a).prod (isClosed_tsupport b))
  have hcomp : HasCompactSupport (Function.uncurry κ) :=
    (a.hasCompactSupport.prod b.hasCompactSupport).of_isClosed_subset
      (isClosed_tsupport (Function.uncurry κ)) ht
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1) (C.U ×ˢ C.U) :=
    C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hp => ⟨hp.2, hp.1⟩)
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, p.2, C.Θ p.2 p.1)) (C.U ×ˢ C.U) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk hθ)
  have hlocal : ContDiffOn ℝ budget (Function.uncurry κ) (C.U ×ˢ C.U) := by
    have he := (((a.contDiff.comp contDiff_fst).of_le (by simp)).contDiffOn.mul
      ((b.contDiff.comp contDiff_snd).of_le (by simp)).contDiffOn).mul
      (hR.comp_contDiffOn (hmap.of_le (by simp)))
    change ContDiffOn ℝ budget
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        a p.1 * b p.2 * R (p.1, p.2, F.Θ p.2 p.1)) (C.U ×ˢ C.U)
    rw [hΘ]
    exact he
  have hglobal : ContDiff ℝ budget (Function.uncurry κ) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases ha : p.1 ∈ tsupport a
    · by_cases hb : p.2 ∈ tsupport b
      · exact hlocal.contDiffAt ((C.isOpen_U.prod C.isOpen_U).mem_nhds
          ⟨hVU (a.tsupport_subset ha), hVU (b.tsupport_subset hb)⟩)
      · have hz : ∀ᶠ x in 𝓝 p.2, b x = 0 := by
          filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hb] with x hx
          exact image_eq_zero_of_notMem_tsupport hx
        have he : Function.uncurry κ =ᶠ[𝓝 p] fun _ => 0 := by
          filter_upwards [(continuous_snd.tendsto p).eventually hz] with q hq
          simp only [Function.uncurry, κ, hq, mul_zero, zero_mul]
        exact contDiffAt_const.congr_of_eventuallyEq he
    · have hz : ∀ᶠ x in 𝓝 p.1, a x = 0 := by
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds ha] with x hx
        exact image_eq_zero_of_notMem_tsupport hx
      have he : Function.uncurry κ =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [(continuous_fst.tendsto p).eventually hz] with q hq
        simp only [Function.uncurry, κ, hq, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  exact ⟨hglobal, hcomp, ht.trans (prod_mono a.tsupport_subset b.tsupport_subset)⟩

end RothschildStein.P1
