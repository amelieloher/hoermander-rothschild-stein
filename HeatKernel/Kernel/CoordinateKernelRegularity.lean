-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TwoSpaceCoordinateMeasure
public import HeatKernel.Kernel.KernelRepresentativeEquality

/-! # Joint smoothness from a coordinate representative

The positive-time measure equivalence transfers a smooth coordinate representative
to the product domain. Fixed-endpoint section regularity identifies it with the
original kernel and transfers joint smoothness to that kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hsmooth : ∀ f, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2) {p | 0 < p.1})

include hself hsemigroup hsmooth

/-- A smooth coordinate representative gives joint smoothness of the original kernel. -/
theorem contDiffOn_heatRepresentativeKernel_of_coordinate_representative
    (v : (Fin (1 + (n + n)) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hrep : (fun z => evaluationKernel (heatRepresentativeEvaluation T u hu hae)
      (timeTwoSpaceCoordinatesAssoc n z).1.1 (timeTwoSpaceCoordinatesAssoc n z).1.2
      (timeTwoSpaceCoordinatesAssoc n z).2) =ᵐ[volume.restrict {z | 0 < z 0}] v) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1.1 p.1.2 p.2)
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) := by
  let e := timeTwoSpaceCoordinatesAssoc n
  have htime (p : (ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) : (e.symm p) 0 = p.1.1 := by
    calc
      (e.symm p) 0 = (e (e.symm p)).1.1 :=
        (timeTwoSpaceCoordinatesAssoc_fst_fst n (e.symm p)).symm
      _ = p.1.1 := congrArg (fun z => z.1.1) (e.apply_symm_apply p)
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => v (e.symm p))
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) := by
    apply hv.comp e.symm.contDiff.contDiffOn
    intro p hp
    change 0 < (e.symm p) 0
    rw [htime]
    exact hp.1
  apply contDiffOn_heatRepresentativeKernel_of_joint_representative T u hu hae
    hself hsemigroup hsmooth (fun p => v (e.symm p)) hvs
  have h := ae_eq_comp_timeTwoSpaceCoordinatesAssoc_symm hrep
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

end HeatKernel
