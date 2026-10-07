-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityFullNoDriftFrame
public import RothschildStein.P1.RightParametrixNoDriftKernel
public import RothschildStein.P1.ParametrixKernelBoundsNoDriftRight
public import RothschildStein.S.CompactKernelIntegral

/-!
# Local solvability without drift, interior Hölder regularity: the separated tail of `P_R` is smooth

For a smooth cutoff `χ` equal to one on an open set `N ⊆ C.U` and any locally integrable input `h`, the
tail potential `P_R((1 - χ) h)(ξ) = ∫ p(ξ, η) (1 - χ(η)) h(η) dη` of the right parametrix kernel
`p(ξ, η) = a(ξ) (b/c)(η) Γ(Θ(η, ξ))` is smooth on `N` (the kernel integral for
`P_R((1 - χ) E_R f)` is separated from the diagonal on the inner ball, so differentiation under the
integral is justified):

* `contDiffOn_cutoff_kernel_noDrift`: `(ξ, η) ↦ (1 - χ(η)) p(ξ, η)` is jointly smooth on `N × ℝ^{n+m}`
  (near the diagonal the cutoff vanishes, away from it `Γ ∘ Θ` is jointly smooth by
  `LiftedChart.contDiffOn_kernelPhi_noDrift`, and `p` vanishes off `supp b`);
* `contDiffOn_tail_integral_noDrift`: the parameter integral against a locally integrable input is smooth on
  `N` (`S.contDiffOn_compactKernelIntegral`, the common compact support being `supp b`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Function
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

section Tail

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))

/-- **Joint smoothness of the separated kernel.** If `χ` is
smooth and equal to one on an open `N ⊆ C.U`, then `(ξ, η) ↦ (1 - χ(η)) p(ξ, η)` is smooth on
`N × ℝ^{n+m}`, where `p = LiftedChart.rightParametrixKernelNoDrift`. -/
theorem contDiffOn_cutoff_kernel_noDrift {N : Set (Fin (n + m) → ℝ)} (hN : IsOpen N) (hNU : N ⊆ C.U)
    {χ : (Fin (n + m) → ℝ) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ x ∈ N, χ x = 1) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (uncurry fun ξ η => (1 - χ η) * C.rightParametrixKernelNoDrift K a b ξ η) (N ×ˢ univ) := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hkey : ∀ z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ),
      (uncurry fun ξ η => (1 - χ η) * C.rightParametrixKernelNoDrift K a b ξ η) z =
        (1 - χ z.2) * ((b z.2 / C.c z.2) * C.kernelPhiNoDrift K a z) := by
    intro z
    simp only [uncurry, LiftedChart.rightParametrixKernelNoDrift, LiftedChart.kernelPhiNoDrift]
    ring
  by_cases hη : p.2 ∈ tsupport (b : (Fin (n + m) → ℝ) → ℝ)
  · by_cases hηN : p.2 ∈ N
    · have hev : (uncurry fun ξ η => (1 - χ η) * C.rightParametrixKernelNoDrift K a b ξ η) =ᶠ[𝓝 p]
          fun _ => (0 : ℝ) := by
        filter_upwards [(hN.prod hN).mem_nhds (show p ∈ N ×ˢ N from ⟨hp.1, hηN⟩)] with z hz
        simp [uncurry, hχ1 z.2 hz.2]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
    · have hne : p.1 ≠ p.2 := fun h => hηN (h ▸ hp.1)
      have hp' : p ∈ C.kernelOffDiagNoDrift := ⟨hNU hp.1, b.tsupport_subset hη, hne⟩
      have hΦ : ContDiffAt ℝ (⊤ : ℕ∞) (C.kernelPhiNoDrift K a) p :=
        (LiftedChart.contDiffOn_kernelPhi_noDrift K.smooth_off_zero a.contDiff.contDiffOn).contDiffAt
          (C.isOpen_kernelOffDiagNoDrift.mem_nhds hp')
      have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
          b z.2 / C.c z.2) := (LiftedChart.contDiff_cutoff_div_density_noDrift (C := C) b.contDiff
            b.tsupport_subset).comp contDiff_snd
      have hχ2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
          1 - χ z.2) := contDiff_const.sub (hχ.comp contDiff_snd)
      have hsm : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
          (1 - χ z.2) * ((b z.2 / C.c z.2) * C.kernelPhiNoDrift K a z)) p :=
        hχ2.contDiffAt.mul (hbc.contDiffAt.mul hΦ)
      exact hsm.congr_of_eventuallyEq (Filter.Eventually.of_forall hkey)
  · have hev : (uncurry fun ξ η => (1 - χ η) * C.rightParametrixKernelNoDrift K a b ξ η) =ᶠ[𝓝 p]
        fun _ => (0 : ℝ) := by
      have hopen : IsOpen ((fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => z.2) ⁻¹'
          (tsupport (b : (Fin (n + m) → ℝ) → ℝ))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl.preimage continuous_snd
      filter_upwards [hopen.mem_nhds hη] with z hz
      have hz' : z.2 ∉ tsupport (b : (Fin (n + m) → ℝ) → ℝ) := hz
      simp [uncurry, rightParametrixKernelNoDrift_eq_zero_of_not_mem_tsupport C K a b hz']
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev

/-- **The separated tail potential is smooth.** For `χ` smooth
and equal to one on the open `N ⊆ C.U` and `h` locally integrable, the function
`ξ ↦ ∫ p(ξ, η) ((1 - χ(η)) h(η)) dη` is smooth on `N`. -/
theorem contDiffOn_tail_integral_noDrift {N : Set (Fin (n + m) → ℝ)} (hN : IsOpen N) (hNU : N ⊆ C.U)
    {χ : (Fin (n + m) → ℝ) → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ x ∈ N, χ x = 1)
    {h : (Fin (n + m) → ℝ) → ℝ} (hh : LocallyIntegrable h volume) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun ξ => ∫ η, C.rightParametrixKernelNoDrift K a b ξ η * ((1 - χ η) * h η)) N := by
  have hks : ∀ ξ η : Fin (n + m) → ℝ, ξ ∈ N → η ∉ tsupport (b : (Fin (n + m) → ℝ) → ℝ) →
      (1 - χ η) * C.rightParametrixKernelNoDrift K a b ξ η = 0 := fun ξ η _ hη => by
    rw [rightParametrixKernelNoDrift_eq_zero_of_not_mem_tsupport C K a b hη, mul_zero]
  have := RothschildStein.S.contDiffOn_compactKernelIntegral (μ := volume) hN
    (K := tsupport (b : (Fin (n + m) → ℝ) → ℝ)) b.hasCompactSupport
    (k := fun ξ η => (1 - χ η) * C.rightParametrixKernelNoDrift K a b ξ η) hks
    (contDiffOn_cutoff_kernel_noDrift K a b hN hNU hχ hχ1) hh
  refine this.congr (fun ξ _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  ring

end Tail

end RothschildStein.P2
