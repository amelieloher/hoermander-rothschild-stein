-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingRegularity

/-!
# Distributional smoothing, descent: the chart lift restricted to a cylinder

The chart lift `T̃ = T ∘ J` (`liftedChartLift`) restricted to a Euclidean cylinder `A × B ⊆ U` is
the lift `φ ↦ T|_A (J_{A×B} ψ)` through the fiber setting of the cylinder
(`FiberIntegration.restrict_lift_apply`), so a representative `w` of the restriction satisfies the
hypothesis of `descent_of_lift`. This gives the chart forms of the descent
(`liftedChart_descent`, `liftedChart_hasWeakWordDeriv_descent`) and the continuous case
(`hasWeakWordDeriv_descent_continuous`) used by the Hölder branch of Thm 11.62.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2
variable {n m : ℕ}

namespace FiberIntegration

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (F : FiberIntegration Uo Vo)

/-- The restriction of the lift to a sub-cylinder is the lift of the restriction through the
fiber setting of the sub-cylinder: `(T̃)|_{Uo'} (ψ) = T|_{Vo'} (J ψ)`. -/
theorem restrict_lift_apply {Uo' : Opens (Fin (n + m) → ℝ)} {Vo' : Opens (Fin n → ℝ)}
    (hU : Uo' ≤ Uo) (hV : Vo' ≤ Vo) (S' : FiberSetting Uo' Vo')
    (T : Distribution Vo ℝ (⊤ : ℕ∞)) (ψ : TestFunction Uo' ℝ (⊤ : ℕ∞)) :
    RothschildStein.S.distributionRestrictionCLM Uo Uo' (F.lift T) ψ =
      RothschildStein.S.distributionRestrictionCLM Vo Vo' T (S'.test ψ) := by
  rw [RothschildStein.S.distributionRestrictionCLM_apply Uo Uo' hU,
    RothschildStein.S.distributionRestrictionCLM_apply Vo Vo' hV, lift_apply]
  congr 1
  apply TestFunction.ext
  intro x
  rw [F.J_apply]
  rfl

/-- If the restriction of the lift to `Uo'` is represented by `w`, the restricted base distribution
satisfies the hypothesis `T (J ψ) = ∫ w ψ` of the descent. -/
theorem restrict_lift_ofFun {Uo' : Opens (Fin (n + m) → ℝ)} {Vo' : Opens (Fin n → ℝ)}
    (hU : Uo' ≤ Uo) (hV : Vo' ≤ Vo) (S' : FiberSetting Uo' Vo')
    (T : Distribution Vo ℝ (⊤ : ℕ∞)) {w : (Fin (n + m) → ℝ) → ℝ}
    (hrepr : RothschildStein.S.distributionRestrictionCLM Uo Uo' (F.lift T) =
      Distribution.ofFun Uo' w volume (⊤ : ℕ∞)) (ψ : TestFunction Uo' ℝ (⊤ : ℕ∞)) :
    RothschildStein.S.distributionRestrictionCLM Vo Vo' T (S'.test ψ) =
      Distribution.ofFun Uo' w volume (⊤ : ℕ∞) ψ := by
  rw [← restrict_lift_apply F hU hV S' T ψ, hrepr]

end FiberIntegration

/-- A cylinder `A × B` (`|B| < ∞`) inside the chart neighborhood has a fiber setting over `A`. -/
theorem liftedChart_cylinderFiberSetting {k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
    {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : LiftedChart w s Ω hΩ X x₀ m) (A : Opens (Fin n → ℝ)) (B : Opens (Fin m → ℝ))
    (hsub : (cylinder A B : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hB : volume (B : Set (Fin m → ℝ)) < ⊤) : FiberSetting (cylinder A B) A :=
  liftedChart_fiberSetting C (cylinder A B) A hsub (fun _ hξ => (mem_cylinder.1 hξ).1)
    ⟨(volume (B : Set (Fin m → ℝ))).toReal, ENNReal.toReal_nonneg,
      (cylinder_fiberBounds (A := A) hB).upper⟩

section Chart

variable {k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

end Chart

section Holder

variable {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

/-- The Hölder branch: if `w` and its lifted word derivative `g` are continuous on
the cylinder, they do not depend on the vertical variable, the fixed slice `x ↦ w(x, t₀)` represents
`T`, and `X_I (w(·, t₀)) = g(·, t₀)` weakly on `A` with both slices continuous (BB p. 609-610). -/
theorem hasWeakWordDeriv_descent_continuous {k : ℕ} (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)))
    (S : FiberSetting (cylinder A B) A) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) (T : Distribution A ℝ (⊤ : ℕ∞))
    {w : (Fin (n + m) → ℝ) → ℝ}
    (hw : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume)
    (hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      T (S.test ψ) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) ψ)
    (I : List (Fin k)) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : hasWeakWordDeriv (triangularLift X P) (cylinder A B) I w g)
    (hwc : ContinuousOn w (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hgc : ContinuousOn g (cylinder A B : Set (Fin (n + m) → ℝ)))
    {t₀ : Fin m → ℝ} (ht₀ : t₀ ∈ (B : Set (Fin m → ℝ))) :
    ContinuousOn (fun x => w (joinPoint x t₀)) (A : Set (Fin n → ℝ)) ∧
      ContinuousOn (fun x => g (joinPoint x t₀)) (A : Set (Fin n → ℝ)) ∧
      representsDistribution A T (fun x => w (joinPoint x t₀)) ∧
      hasWeakWordDeriv X A I (fun x => w (joinPoint x t₀)) (fun x => g (joinPoint x t₀)) ∧
      ∀ x ∈ (A : Set (Fin n → ℝ)), ∀ t ∈ (B : Set (Fin m → ℝ)),
        w (joinPoint x t) = w (joinPoint x t₀) ∧ g (joinPoint x t) = g (joinPoint x t₀) := by
  obtain ⟨hrep, hwae⟩ := descent_of_lift S hη T hw hT
  obtain ⟨hwd, hgae⟩ := hasWeakWordDeriv_descent X P hXt hX S hη T hw hT I hg
  have hmaps : ∀ f : (Fin (n + m) → ℝ) → ℝ,
      ContinuousOn f (cylinder A B : Set (Fin (n + m) → ℝ)) →
        ContinuousOn (fun x => f (joinPoint x t₀)) (A : Set (Fin n → ℝ)) := fun f hf =>
    hf.comp (continuous_joinPoint_left t₀).continuousOn fun y hy =>
      joinPoint_mem_cylinder.2 ⟨hy, ht₀⟩
  have hws : ∀ x ∈ (A : Set (Fin n → ℝ)), fiberAvg w η x = w (joinPoint x t₀) := fun x hx =>
    fiberAvg_eq_slice hwc hwae hη hx ht₀
  have hgs : ∀ x ∈ (A : Set (Fin n → ℝ)), fiberAvg g η x = g (joinPoint x t₀) := fun x hx =>
    fiberAvg_eq_slice hgc hgae hη hx ht₀
  have hwA : fiberAvg w η =ᵐ[volume.restrict (A : Set (Fin n → ℝ))]
      fun x => w (joinPoint x t₀) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' A.isOpen.measurableSet]
    exact Eventually.of_forall hws
  have hgA : fiberAvg g η =ᵐ[volume.restrict (A : Set (Fin n → ℝ))]
      fun x => g (joinPoint x t₀) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' A.isOpen.measurableSet]
    exact Eventually.of_forall hgs
  have hwcA := hmaps w hwc
  refine ⟨hwcA, hmaps g hgc, ⟨hwcA.locallyIntegrableOn A.isOpen.measurableSet, ?_⟩,
    RothschildStein.S.hasWeakWordDeriv_congr_ae X A hwd hwA hgA, fun x hx t ht => ?_⟩
  · rw [hrep.2]
    exact Distribution.ofFun_congr_ae hwA
  · exact ⟨eq_slice_of_continuousOn hwc hwae x hx t ht t₀ ht₀,
      eq_slice_of_continuousOn hgc hgae x hx t ht t₀ ht₀⟩

end Holder

end RothschildStein.P2
