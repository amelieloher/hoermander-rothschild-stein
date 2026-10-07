-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularKernelModelMultiplier
public import RothschildStein.P1.PrincipalModelKernel

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

/-- A model cutoff vanishing near zero
makes the entire parameter-dependent principal model family globally
smooth, across every arbitrary value at its pole (BB p. 557). -/
theorem PrincipalTerm.transfer_cutoff_model_contDiff {F : KernelFrame (n+m)}
    (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n+m) → ℝ)}ᶜ)
    (φ : (Fin (n+m) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (heφ : φ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 0) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) =>
        φ q.2.2 * t.modelKernel q.1 q.2.1 q.2.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2.2 = 0
  · have he : (fun z : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) =>
        φ z.2.2 * t.modelKernel z.1 z.2.1 z.2.2) =ᶠ[𝓝 q] fun _ => 0 := by
      have ht := continuous_snd.snd.tendsto q
      rw [hq] at ht
      filter_upwards [heφ.comp_tendsto ht] with z hz
      simp only [Function.comp_apply] at hz
      rw [hz, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have ho : IsOpen {z : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) |
        z.2.2 ≠ 0} := isOpen_compl_singleton.preimage continuous_snd.snd
    exact ((hφ.comp contDiff_snd.snd).contDiffAt).mul
      ((t.modelKernel_contDiffOn hΓ).contDiffAt (ho.mem_nhds hq))

/-- Whole principal cutoff kernels are
actual regular kernels at every finite regularity budget, on the
original chart (BB p. 557, Theorem 11.24). -/
theorem LiftedChart.isRegularKernel_principalTransferCutoff
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n+m) → ℝ)}ᶜ)
    (φ : (Fin (n+m) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (heφ : φ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 0) (budget : ℕ) :
    IsRegularKernel F budget (fun ξ η => φ (F.Θ η ξ) * t.kernel ξ η) := by
  have hs := t.transfer_cutoff_model_contDiff hΓ φ hφ heφ
  have hr := C.isRegularKernel_cutoff_model F hΘ hVU budget t.a t.b _ (hs.of_le (by simp))
  convert hr using 1
  funext ξ η
  simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel]
  ring

end RothschildStein.P1
