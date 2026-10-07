-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNear
public import RothschildStein.P2.SobolevInterpolationFarPart

/-!
# Sobolev interpolation, near and far parts: the near and far parts are measurable in the output point

The near part `II(ξ) = ∫ k(ξ, η) φ_ε(ξ, η) g(η) dη` and the far part
`I(ξ) = ∫ k(ξ, η) (1 - φ_ε(ξ, η)) g(η) dη` of the integral `F g(ξ) = ∫ k(ξ, η) g(η) dη` of a
type-1 operator are defined here (`nearPart`, `farPart`). Their measurability in `ξ` (needed to
apply the `L^p` bound of Schur's test) follows from the joint measurability of the cut kernel
(`PatchKernel.measurable`) and the continuity of the cutoff on `U × U`
(`aestronglyMeasurable_kernelIntegral`, `aestronglyMeasurable_radialCutoff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The near part `II(ξ) = ∫ k(ξ, η) φ_ε(ξ, η) g(η) dη`, with `φ_ε` the cutoff of
the radial cutoff construction centred at the output point `ξ` (`radialCutoff C ν ξ (ε/4) ε`). -/
def nearPart (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {F : KernelFrame (n + m)} {lam : ℕ} (T : TypeOperator F lam) (ε : ℝ)
    (g : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  ∫ η, T.kernel ξ η * radialCutoff C ν ξ (ε / 4) ε η * g η

/-- The far part `I(ξ) = ∫ k(ξ, η) (1 - φ_ε(ξ, η)) g(η) dη`. -/
def farPart (C : LiftedChart w s Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {F : KernelFrame (n + m)} {lam : ℕ} (T : TypeOperator F lam) (ε : ℝ)
    (g : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  ∫ η, T.kernel ξ η * (1 - radialCutoff C ν ξ (ε / 4) ε η) * g η

variable {C : LiftedChart w s Ω hΩ X x₀ m} {S V : Set (Fin (n + m) → ℝ)}
  {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- **Measurability of a kernel integral in the output point**: for a patch kernel `κ`, a weight
`Ψ(ξ, η)` that is a.e.-measurable on `V × V` and `g` a.e.-measurable on `V`, the function
`ξ ↦ ∫ κ(ξ, η) Ψ(ξ, η) g(η) dη` is a.e.-measurable on `V`. -/
theorem aestronglyMeasurable_kernelIntegral (h : C.PatchKernel S V κ)
    {Ψ : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ}
    (hΨ : AEStronglyMeasurable Ψ ((volume.restrict V).prod (volume.restrict V)))
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict V)) :
    AEStronglyMeasurable (fun ξ => ∫ η, κ ξ η * Ψ (ξ, η) * g η) (volume.restrict V) := by
  have hVm : MeasurableSet V := h.measurableSet
  have hsl : AEStronglyMeasurable (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      sliceKernel S κ z.1 z.2) ((volume.restrict V).prod (volume.restrict V)) :=
    h.measurable.aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      sliceKernel S κ z.1 z.2 * Ψ z * g z.2) ((volume.restrict V).prod (volume.restrict V)) :=
    (hsl.mul hΨ).mul hg.comp_snd
  refine hF.integral_prod_right'.congr ?_
  filter_upwards [ae_restrict_mem hVm] with ξ hξ
  have hF0 : ∀ η ∉ V, κ ξ η * Ψ (ξ, η) * g η = 0 := by
    intro η hη
    have hne : ξ ≠ η := fun e => hη (e ▸ hξ)
    rw [h.support ξ η hne (Or.inr hη), zero_mul, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0]
  refine setIntegral_congr_ae hVm ?_
  filter_upwards [C.ae_ne ξ] with η hηξ hη
  rw [sliceKernel_of_mem (h.subset hξ) (h.subset hη) (Ne.symm hηξ)]

/-- The cutoff `φ_ε(ξ, η) = radialCutoff C ν ξ s r η` is a.e.-measurable on `V × V` for
`V ⊆ U` (it is continuous there). -/
theorem aestronglyMeasurable_radialCutoff (ν : G2.HomogeneousNorm C.G) (hVm : MeasurableSet V)
    (hVU : V ⊆ C.U) (s' r' : ℝ) :
    AEStronglyMeasurable (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      radialCutoff C ν z.1 s' r' z.2) ((volume.restrict V).prod (volume.restrict V)) := by
  rw [Measure.prod_restrict]
  set G : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ :=
    fun z => cutoffProfile ((ν (C.Θ z.1 z.2) - s') / (r' - s')) with hG
  have hΘ : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ z.1 z.2)
      (V ×ˢ V) := C.theta_smooth.continuousOn.mono (prod_mono hVU hVU)
  have hcp : Continuous cutoffProfile := by
    unfold cutoffProfile
    exact Real.smoothTransition.continuous.comp (by fun_prop)
  have hGc : ContinuousOn G (V ×ˢ V) :=
    hcp.comp_continuousOn (((ν.gauge.1.comp_continuousOn hΘ)).sub continuousOn_const
      |>.div_const _)
  refine (hGc.aestronglyMeasurable (hVm.prod hVm)).congr ?_
  refine (ae_restrict_iff' (hVm.prod hVm)).2 (ae_of_all _ fun z hz => ?_)
  show G z = radialCutoff C ν z.1 s' r' z.2
  rw [radialCutoff_apply_of_mem C ν z.1 s' r' (hVU hz.2)]

/-- The near part is a.e.-measurable in the output point. -/
theorem aestronglyMeasurable_nearPart {F : KernelFrame (n + m)} {lam : ℕ} (T : TypeOperator F lam)
    (h : C.PatchKernel S V T.kernel) (ν : G2.HomogeneousNorm C.G) (ε : ℝ)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict V)) :
    AEStronglyMeasurable (nearPart C ν T ε g) (volume.restrict V) :=
  aestronglyMeasurable_kernelIntegral (Ψ := fun z => radialCutoff C ν z.1 (ε / 4) ε z.2) h
    (aestronglyMeasurable_radialCutoff ν h.measurableSet (h.subset.trans h.subset_U) (ε / 4) ε) hg

/-- The far part is a.e.-measurable in the output point. -/
theorem aestronglyMeasurable_farPart {F : KernelFrame (n + m)} {lam : ℕ} (T : TypeOperator F lam)
    (h : C.PatchKernel S V T.kernel) (ν : G2.HomogeneousNorm C.G) (ε : ℝ)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : AEStronglyMeasurable g (volume.restrict V)) :
    AEStronglyMeasurable (farPart C ν T ε g) (volume.restrict V) :=
  aestronglyMeasurable_kernelIntegral (Ψ := fun z => 1 - radialCutoff C ν z.1 (ε / 4) ε z.2) h
    (aestronglyMeasurable_const.sub
      (aestronglyMeasurable_radialCutoff ν h.measurableSet (h.subset.trans h.subset_U) (ε / 4) ε))
    hg

end RothschildStein.P2
