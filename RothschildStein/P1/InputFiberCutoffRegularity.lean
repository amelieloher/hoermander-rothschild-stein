-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernelInputSmoothness
public import RothschildStein.P1.RadialGaugeCutoff
public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Cutting out the pole makes the actual type
kernel input fiber C¹ across its arbitrary diagonal value. -/
theorem isTypeKernel_contDiffOn_inputCutoff {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1) (ε : ℝ) :
    ContDiffOn ℝ 1 (fun η => (1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) * κ ξ η)
      (F.V : Set (Fin (n + m) → ℝ)) := by
  have hξU := hF.closure_subset (subset_closure hξ)
  have hΘ : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => C.Θ η ξ)
      (F.V : Set (Fin (n + m) → ℝ)) :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun η hη => ⟨hF.closure_subset (subset_closure hη), hξU⟩)
  have hcut : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => θ (C.G.dilate ε⁻¹ (C.Θ η ξ)))
      (F.V : Set (Fin (n + m) → ℝ)) :=
    (hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).comp_contDiffOn hΘ
  have hκs := C.isTypeKernel_contDiffOn_input hF hκ hξU
  intro η hη
  have hat : ContDiffAt ℝ 1
      (fun ζ => (1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) * κ ξ ζ) η := by
    by_cases he : η = ξ
    · subst η
      have ht := ((G2.contDiff_dilate C.G ε⁻¹).comp_contDiffOn hΘ).continuousOn.continuousAt
        (F.V.isOpen.mem_nhds hξ)
      have hz : C.G.dilate ε⁻¹ (C.Θ ξ ξ) = 0 := by
        rw [(C.chart ξ hξU).2.2.2.2, G2.dilate_zero]
      have hlim := ht.tendsto
      simp only [Function.comp_apply] at hlim
      rw [hz] at hlim
      have hone := heθ.comp_tendsto hlim
      have hzero : (fun ζ => (1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) * κ ξ ζ) =ᶠ[𝓝 ξ]
          fun _ => 0 := by
        filter_upwards [hone] with ζ hζ
        simp only [Function.comp_apply] at hζ
        rw [hζ, sub_self, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · have hm : η ∈ ((F.V : Set (Fin (n + m) → ℝ)) \ {ξ}) := ⟨hη, he⟩
      exact ((contDiffAt_const.sub (hcut.contDiffAt (F.V.isOpen.mem_nhds hη))).of_le
        (by simp)).mul (hκs.contDiffAt ((F.V.isOpen.sdiff isClosed_singleton).mem_nhds hm))
  exact hat.contDiffWithinAt

end RothschildStein.P1.LiftedChart
