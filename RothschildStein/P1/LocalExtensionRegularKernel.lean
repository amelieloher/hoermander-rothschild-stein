-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ChartRegularKernel
public import RothschildStein.P1.LocalCoefficientExtension

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

/-- Replacing a local coefficient by a
smooth extension agreeing over the compact cutoff patch near the pole
changes the actual kernel by a compact smooth remainder. This gives the
annular part of the local Taylor construction (BB pp. 548–549). -/
theorem LiftedChart.isRegularKernel_local_extension_difference
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (budget : ℕ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (A B : ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ) → ℝ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A (p, F.Θ p.2 p.1))
      (C.U ×ˢ C.U))
    (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    (g : (Fin (n + m) → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin (n + m) → ℝ)}ᶜ)
    (ε : ℝ) (hε : 0 < ε)
    (he : ∀ p ∈ tsupport a ×ˢ tsupport b, ∀ u : Fin (n + m) → ℝ,
      ‖u‖ ≤ ε → B (p, u) = A (p, u)) :
    IsRegularKernel F budget (fun ξ η => a ξ * b η *
      ((A ((ξ, η), F.Θ η ξ) - B ((ξ, η), F.Θ η ξ)) * g (F.Θ η ξ))) := by
  let κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ :=
    fun ξ η => a ξ * b η *
      ((A ((ξ, η), F.Θ η ξ) - B ((ξ, η), F.Θ η ξ)) * g (F.Θ η ξ))
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
  have hθF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => F.Θ p.2 p.1)
      (C.U ×ˢ C.U) := by rw [hΘ]; exact hθ
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p, F.Θ p.2 p.1))
      (C.U ×ˢ C.U) := contDiffOn_id.prodMk hθF
  have hlocal : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry κ) (C.U ×ˢ C.U) := by
    intro p hp
    have hnhds := (C.isOpen_U.prod C.isOpen_U).mem_nhds hp
    have hθAt := hθF.contDiffAt hnhds
    by_cases hu : F.Θ p.2 p.1 = 0
    · have hn : ContinuousAt
          (fun q : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => ‖F.Θ q.2 q.1‖) p :=
        hθAt.continuousAt.norm
      have hsmall : ∀ᶠ q in 𝓝 p, ‖F.Θ q.2 q.1‖ < ε :=
        hn.tendsto.eventually (Iio_mem_nhds (by simpa only [hu, norm_zero] using hε))
      have hz : Function.uncurry κ =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [hsmall] with q hq
        by_cases ha : a q.1 = 0
        · simp only [Function.uncurry, κ, ha, zero_mul]
        by_cases hb : b q.2 = 0
        · simp only [Function.uncurry, κ, hb, mul_zero, zero_mul]
        have heq := he q ⟨subset_tsupport a ha, subset_tsupport b hb⟩
          (F.Θ q.2 q.1) hq.le
        simp only [Function.uncurry, κ, heq, sub_self, zero_mul, mul_zero]
      exact (contDiffAt_const.congr_of_eventuallyEq hz).contDiffWithinAt
    · have hprod := ((a.contDiff.comp contDiff_fst).contDiffAt.mul
          (b.contDiff.comp contDiff_snd).contDiffAt).mul
        ((hA.contDiffAt hnhds).sub (hB.comp_contDiffOn hmap |>.contDiffAt hnhds) |>.mul
          ((hg.contDiffAt (isOpen_compl_singleton.mem_nhds hu)).comp p hθAt))
      exact hprod.contDiffWithinAt
  have hglobal : ContDiff ℝ budget (Function.uncurry κ) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases ha : p.1 ∈ tsupport a
    · by_cases hb : p.2 ∈ tsupport b
      · exact (hlocal.of_le (by simp)).contDiffAt ((C.isOpen_U.prod C.isOpen_U).mem_nhds
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
