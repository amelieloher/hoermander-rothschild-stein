-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingZeroTriangularLift
public import RothschildStein.P1.PaddingDistributionDescent
public import RothschildStein.P1.WordReindex
public import RothschildStein.P1.PaddingLieWordDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- Every original weighted word derivative of the padded
representative descends to the same word derivative on the base.
The derivative representative is also independent of the fiber almost
everywhere. This uses the actual tensor distribution and the original words. -/
theorem paddingDistributionTensor_weakWord_descent {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) ≠ ⊤)
    (η : _root_.TestFunction J ℝ ⊤) (hη : ∫ z, η z = 1)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (v g : (Fin (n + d) → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (P2.cylinder Ω J)
      (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (P2.cylinder Ω J) v volume (⊤ : ℕ∞))
    (I : List (Fin (q + 1)))
    (hg : hasWeakWordDeriv (paddingVectorFields (d := d) X) (P2.cylinder Ω J)
      (I.map paddingGeneratorIndex) v g) :
    hasWeakWordDeriv X Ω I (P2.fiberAvg v η) (P2.fiberAvg g η) ∧
      g =ᵐ[volume.restrict (P2.cylinder Ω J : Set (Fin (n + d) → ℝ))]
        fun ξ => P2.fiberAvg g η (basePoint ξ) := by
  let S : P2.FiberSetting (P2.cylinder Ω J) Ω := fiberSetting_padding_cylinder Ω J hJ
  have hpair (ψ : _root_.TestFunction (P2.cylinder Ω J) ℝ ⊤) :
      T (S.test ψ) = Distribution.ofFun (P2.cylinder Ω J) v volume (⊤ : ℕ∞) ψ := by
    rw [← paddingFiberTestCLM_eq_fiberSetting_test Ω J S ψ,
      ← paddingDistributionTensorOneCLM_apply]
    exact congrArg (fun D : Distribution (P2.cylinder Ω J) ℝ (⊤ : ℕ∞) => D ψ) hT
  have he : paddingVectorFields (d := d) X ∘ paddingGeneratorIndex =
      triangularLift X (0 : Fin (q + 1) → Fin d → MvPolynomial (Fin (n + d)) ℝ) := by
    rw [← paddingBaseFields_eq_zero_triangularLift]
    funext i
    exact paddingVectorFields_generatorIndex X i
  have hg' := (hasWeakWordDeriv_map_indices_iff _ _ _ _ v g).mp hg
  rw [he] at hg'
  exact P2.hasWeakWordDeriv_descent X 0
    (contDiffOn_zero_triangularLift_cylinder Ω J X hX) hX S hη T hv hpair I hg'

end RothschildStein.P1
