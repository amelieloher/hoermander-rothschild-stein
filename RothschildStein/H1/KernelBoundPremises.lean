-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.AssemblyInputs
public import RothschildStein.H1.FiniteOperatorHomogeneity
public import RothschildStein.H1.OpenShellBoundary
public import RothschildStein.G2.CoordinateIntegration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- The general-operator kernel bound used in the one-operator theorem
(BB Theorem 6.20(1), p. 269). -/
theorem FundamentalKernel.generalKernelBounds (K : FundamentalKernel G H) : GeneralKernelBounds K := by
  intro D k hD
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (D.apply K) ({(0 : Fin N → ℝ)}ᶜ) := by
    unfold SmoothDifferentialOperator.apply
    apply ContDiffOn.sum
    intro a ha
    apply (D.smooth_coefficient a ha).contDiffOn.mul
    apply contDiffOn_infty.mpr
    intro n
    exact contDiffOn_euclideanPartial_finite U a n K
      (K.smooth_off_zero.of_le (by simp))
  have hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → D.apply K (G.dilate t x) =
      t ^ (2 - (G.homogeneousDimension : ℝ) - k) * D.apply K x := by
    intro t ht x hx
    exact differentialOperator_punctured_homogeneity_finite G D hD
      (fun _ _ => K.smooth_off_zero.of_le (by simp)) K.homogeneous ht hx
  exact ⟨hc, hh, homogeneous_bound G H.norm _ hc.continuousOn hh⟩

/-- The kernel satisfies strict-shell radial-weight cancellation, with
absolute integrability (BB Corollary 6.31, p. 280). -/
theorem FundamentalKernel.kernelShellCancellation (K : FundamentalKernel G H) :
    KernelShellCancellation K := by
  intro D hD r R hr hrR Φ hΦ
  have hc := (K.generalKernelBounds D 2 hD).1.continuousOn
  have hreg : ∀ a ∈ D.indices, ContDiffOn ℝ (∑ j, a j : ℕ) (K : (Fin N → ℝ) → ℝ)
      ({(0 : Fin N → ℝ)}ᶜ) := fun _ _ => K.smooth_off_zero.of_le (by simp)
  have hz := integral_homogeneousDerivative_radialWeight_zero G D
    (by norm_num : (0 : ℝ) < 2) hD H.norm.gauge K.smooth_off_zero.continuousOn
    hreg K.homogeneous hr hrR hΦ
  have hcW : ContinuousOn (fun x => D.apply K x * Φ (H.norm x)) (gaugeShell H.norm r R) :=
    (hc.mono (gaugeShell_subset_punctured H.norm.gauge hr)).mul
      (hΦ.comp H.norm.gauge.1.continuousOn (fun _ hx => hx))
  refine ⟨(hcW.integrableOn_compact (isCompact_gaugeShell H.norm.gauge r R)).mono_set
    (fun _ hx => ⟨hx.1.le, hx.2.le⟩), ?_⟩
  rw [integral_openGaugeShell_eq_closed G H.norm.gauge hr (hr.trans hrR)]
  exact hz

end RothschildStein.H1
