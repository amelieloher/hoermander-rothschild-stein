-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalLocalWeightConjugation
public import HeatKernel.Gaussian.LocalFormDistanceWeight

/-! # Conjugation by truncated Carnot distance weights

The truncated distance weight gives the concrete weighted operator bound for
the heat operators associated with the horizontal energy form.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein TopologicalSpace
namespace HeatKernel.Gaussian

/-- Truncated Carnot distance conjugation of the horizontal heat operator
satisfies the Gaussian weighted norm bound. -/
theorem norm_horizontalHeat_carnot_distance_conjugation_le {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (x y : CarnotPoint G hq hqpos hspan) (a : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    let μ : Measure (CarnotPoint G hq hqpos hspan) :=
      (volume : Measure (Fin N → ℝ)).restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ));
    ‖(distanceExponentialMultiplication μ x y a).comp
      ((horizontalHeatOperator ⊤ (G.horizontalFields hq) t.toNNReal).comp (distanceExponentialMultiplication μ x y (-a)))‖ ≤ Real.exp (a ^ 2 * t) := by
  intro μ
  let ψ := fun z : CarnotPoint G hq hqpos hspan ↦ min (dist x z) (dist x y)
  have hψ : AEStronglyMeasurable ψ μ :=
    (lipschitzWith_truncated_distance x y).continuous.aestronglyMeasurable
  obtain ⟨hm, g, hg, hb, _⟩ := truncated_distance_local_form_gradient G hq hqpos hspan x y
  have he : ∀ b, distanceExponentialMultiplication μ x y b =
      exponentialMultiplication μ ψ hψ (dist x y) (abs_truncated_distance_le x y) b := by
    intro b
    ext f
    filter_upwards [coeFn_distanceExponentialMultiplication μ x y b f,
      coeFn_exponentialMultiplication μ ψ hψ (dist x y) (abs_truncated_distance_le x y) b f]
      with z hz hw
    exact hz.trans hw.symm
  rw [he a, he (-a)]
  exact norm_horizontalHeat_exponential_conjugation_le (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) ψ g hm hg (dist x y)
    (abs_truncated_distance_le x y) a hb ht

end HeatKernel.Gaussian
