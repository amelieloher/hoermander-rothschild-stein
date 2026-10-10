-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelJointSmoothness

/-! # Joint kernel regularity in time and spatial-pair coordinates

Reassociation of product coordinates puts joint kernel smoothness in the usual
form with time followed by the pair of spatial endpoints.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein

/-- Reassociation preserves smoothness on the positive-time product domain. -/
theorem contDiffOn_positive_time_reassociate {n : ℕ}
    (k : ((ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) → ℝ)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) k
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => k ((p.1, p.2.1), p.2.2))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => ((p.1, p.2.1), p.2.2)) :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
      (contDiff_snd.comp contDiff_snd)
  exact hk.comp hs.contDiffOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)

/-- The representative kernel is jointly smooth in time and the ordered pair of endpoints. -/
theorem contDiffOn_heatRepresentativeKernel_positive {n q : ℕ}
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
    (hheat : ∀ t, 0 < t → ∀ f x, deriv (fun s => u s f x) t =
      sumSquares (G.horizontalFields hq) (u t f) x) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        evaluationKernel (heatRepresentativeEvaluation T u hu hae) p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  exact contDiffOn_positive_time_reassociate _
    (contDiffOn_heatRepresentativeKernel_of_classical_representatives
      G hq hspan T u hu hae hself hsemigroup hsmooth hheat)

end HeatKernel
