-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateKernelRegularity
public import HeatKernel.Kernel.SmoothTwoSpaceRepresentatives

/-! # Joint kernel smoothness from the two-block weak equation

The two-block Hörmander equation produces a smooth coordinate representative.
Spacetime section regularity identifies that representative with the original
kernel at every positive time and spatial pair.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open Hormander.Interface RothschildStein

/-- The weak two-block equation implies joint smoothness of the representative kernel. -/
theorem contDiffOn_heatRepresentativeKernel_of_weak_two_space_equation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})
    (hweak : HasWeakHormanderEquation {z | 0 < z 0} (horizontalTwoSpaceHeatFields G hq) 0 0
      (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinatesAssoc n z).1.1 (timeTwoSpaceCoordinatesAssoc n z).1.2
        (timeTwoSpaceCoordinatesAssoc n z).2)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2)
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) := by
  have hbracket : LieAlgebraSpansOn {z | 0 < z 0} (horizontalTwoSpaceHeatFields G hq) := by
    intro z _
    exact lieAlgebraSpansOn_horizontalTwoSpaceHeatFields G hq hspan z (Set.mem_univ z)
  obtain ⟨v, hv, hrep⟩ := Hormander.Interface.exists_smooth_aeRepresentative
    (isOpen_positive_time (n + n)) (horizontalTwoSpaceHeatFields G hq) 0 0
    (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      (timeTwoSpaceCoordinatesAssoc n z).1.1 (timeTwoSpaceCoordinatesAssoc n z).1.2
      (timeTwoSpaceCoordinatesAssoc n z).2)
    (fun i => (contDiff_horizontalTwoSpaceHeatFields G hq i).contDiffOn)
    hbracket contDiffOn_const hweak
  exact contDiffOn_heatRepresentativeKernel_of_coordinate_representative
    T u hu hae hself hsemigroup hsmooth v hv hrep

end HeatKernel
