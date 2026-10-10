-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.DistanceExponentialOperator
public import HeatKernel.Geometry.LipschitzLocalForm
import Mathlib.Tactic

/-! # Local form gradients of truncated distance weights

The bounded endpoint weight has a unit weak horizontal gradient compatible
with every local representative in the closed horizontal form domain.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
open scoped BigOperators
namespace HeatKernel.Gaussian

/-- The truncated endpoint distance is a local energy function with a unit
weak gradient agreeing with every local closed-form representative. -/
theorem truncated_distance_local_form_gradient {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) :
    let ψ := fun z : CarnotPoint G hq hqpos hspan ↦ min (dist x z) (dist x y);
    MemLocalEnergy ⊤ (G.horizontalFields hq) ψ ∧
      ∃ g : Fin q → (Fin N → ℝ) → ℝ,
        (∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] ψ (g i)) ∧
        (∀ᵐ z ∂(volume : Measure (Fin N → ℝ)), ∑ i, g i z ^ 2 ≤ 1) ∧
        ∀ (V : Opens (Fin N → ℝ)) (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)),
          energyInclusion ⊤ (G.horizontalFields hq) u =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] ψ →
          ∀ i, energyGradient ⊤ (G.horizontalFields hq) u i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g i := by
  obtain ⟨hm, g, hg, hb, heq⟩ := CarnotPoint.exists_local_form_gradient G hq hqpos hspan
    (lipschitzWith_truncated_distance x y)
  refine ⟨hm, g, hg, ?_, heq⟩
  filter_upwards [hb] with z hz
  have hs : 0 ≤ ∑ i, g i z ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have he := Real.sq_sqrt hs
  have hn := Real.sqrt_nonneg (∑ i, g i z ^ 2)
  norm_num only [NNReal.coe_one] at hz
  nlinarith

end HeatKernel.Gaussian
