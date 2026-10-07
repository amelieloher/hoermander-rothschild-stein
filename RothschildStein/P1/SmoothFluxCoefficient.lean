-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CompactKernelIntegral
public import RothschildStein.H1.FieldCutoffSupport
public import RothschildStein.H1.FieldSubtractConstant

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1

variable {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A model cutoff vanishing near the pole
makes a punctured jointly smooth parameter family globally smooth. -/
theorem contDiff_parameterized_pole_mul_cutoff
    (Ψ : E × (Fin N → ℝ) → ℝ)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {q | q.2 ≠ 0})
    (H : (Fin N → ℝ) → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (heH : H =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : E × (Fin N → ℝ) => Ψ q * H q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hu : q.2 = 0
  · have hz : ∀ᶠ z in 𝓝 q, H z.2 = 0 := by
      have heHq : H =ᶠ[𝓝 q.2] fun _ => 0 := by rw [hu]; exact heH
      exact (continuous_snd.tendsto q).eventually heHq
    have he : (fun z : E × (Fin N → ℝ) => Ψ z * H z.2) =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [hz] with z hz
      rw [hz, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (hΨ.contDiffAt ((isOpen_compl_singleton.preimage continuous_snd).mem_nhds hu)).mul
      (hH.comp contDiff_snd).contDiffAt

/-- The actual annular flux coefficient ∫Ψ Yχ
is smooth in all endpoint parameters. χ=1-η has a compactly supported
field derivative and its near-pole derivative is zero; no smooth
extension of the singular family itself is assumed. -/
theorem contDiff_exteriorFluxCoefficient [LocallyCompactSpace E]
    (Ψ : E × (Fin N → ℝ) → ℝ)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {q | q.2 ≠ 0})
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (η : (Fin N → ℝ) → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : E => ∫ u, Ψ (p, u) * fieldDerivative Y (fun v => 1 - η v) u) := by
  let H := fieldDerivative Y (fun v => 1 - η v)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [show H = fun u => -fieldDerivative Y η u from H1.fieldDerivative_one_sub_C1 Y (hη.of_le (by simp))]
    exact (H1.smooth_fieldDerivative Y hY η hη).neg
  have heH : H =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
    rw [show H = fun u => -fieldDerivative Y η u from H1.fieldDerivative_one_sub_C1 Y (hη.of_le (by simp))]
    filter_upwards [H1.fieldDerivative_cutoff_eventually_zero Y heη] with u hu
    rw [hu, neg_zero]
  have hΦ := contDiff_parameterized_pole_mul_cutoff Ψ hΨ H hH heH
  have hc := compactKernelIntegral_contDiff _ hΦ (tsupport η) hsη
  have he : (fun p : E => ∫ u in tsupport η, Ψ (p, u) * H u) =
      (fun p : E => ∫ u, Ψ (p, u) * H u) := by
    funext p
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hzero : fieldDerivative Y η u = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hu (S.tsupport_fieldDerivative_subset Y η h))
    have heq := congrFun (H1.fieldDerivative_one_sub_C1 Y (hη.of_le (by simp))) u
    change H u = -fieldDerivative Y η u at heq
    rw [heq, hzero, neg_zero, mul_zero]
  rw [he] at hc
  exact hc

end RothschildStein.P1
