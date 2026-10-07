-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.PulledCoefficients
public import RothschildStein.Distribution.RestrictionForcing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- the equation on the original open set transfers
exactly to the pulled compact coefficient patch on its frame ball.
The original equation, not a patched forcing identity, is the input. -/
theorem localPatch_distributionEquation {k N : ℕ} (hN : 0 < N)
    (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (x₀ : Fin N → ℝ)
    (P : Hormander.F.LocalPatch hN (Hormander.F.coordinateEquiv N '' (Ω : Set (Fin N → ℝ)))
      (Hormander.F.pushVectorFields X) (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
      (Hormander.F.coordinateEquiv N x₀))
    (B : Opens (Fin N → ℝ))
    (hB : (B : Set (Fin N → ℝ)) = (Hormander.F.coordinateEquiv N) ⁻¹'
      Metric.ball (Hormander.F.coordinateEquiv N x₀) P.radius)
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω X c hX hc ψ) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) ψ) :
    ∀ ψ : TestFunction B ℝ (⊤ : ℕ∞),
      restrictComplexDistribution Ω B T
        (adjointTest B
          (fun i x => (Hormander.F.coordinateEquiv N).symm (P.extendedX i (Hormander.F.coordinateEquiv N x)))
          (fun x => P.extendedC (Hormander.F.coordinateEquiv N x))
          (fun i => (contDiff_pulledVectorField (P.extendedX i) (P.extendedX_smooth i)).contDiffOn)
          (P.extendedC_smooth.comp (Hormander.F.coordinateEquiv N).contDiff).contDiffOn ψ) =
      Distribution.ofFun B g volume (⊤ : ℕ∞) ψ := by
  have hBΩ : B ≤ Ω := by
    change (B : Set (Fin N → ℝ)) ⊆ (Ω : Set (Fin N → ℝ))
    rw [hB]
    exact pulledPatch_ball_subset hN (Ω : Set (Fin N → ℝ)) X c x₀ P
  have hbase := restrictComplexDistribution_equation Ω B hBΩ T
    (Distribution.ofFun Ω g volume (⊤ : ℕ∞)) X c hX hc heq
  have hgi : LocallyIntegrableOn g (Ω : Set (Fin N → ℝ)) volume :=
    hg.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  rw [restrictComplexDistribution_ofFun Ω B hBΩ g hgi] at hbase
  apply distributionEquation_of_coefficients_eqOn B (restrictComplexDistribution Ω B T)
    (Distribution.ofFun B g volume (⊤ : ℕ∞)) X _ c _
    (fun i => (hX i).mono hBΩ) _ (hc.mono hBΩ) _ _ _ hbase
  · intro i x hx
    have hx' : x ∈ (Hormander.F.coordinateEquiv N) ⁻¹'
        Metric.ball (Hormander.F.coordinateEquiv N x₀) P.radius := by simpa only [hB] using hx
    exact (pulledPatch_fields_eqOn hN (Ω : Set (Fin N → ℝ)) X c x₀ P i hx').symm
  · intro x hx
    have hx' : x ∈ (Hormander.F.coordinateEquiv N) ⁻¹'
        Metric.ball (Hormander.F.coordinateEquiv N x₀) P.radius := by simpa only [hB] using hx
    exact (pulledPatch_multiplier_eqOn hN (Ω : Set (Fin N → ℝ)) X c x₀ P hx').symm

end RothschildStein.Distribution
