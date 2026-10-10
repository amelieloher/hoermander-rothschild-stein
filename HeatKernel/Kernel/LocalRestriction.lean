-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ContinuousRepresentatives

/-! # Restricting L² representatives to compact subsets

Restriction of measure followed by pullback to a measurable subtype is bounded in L².
This supplies the compact comparison map for local bounded evaluations.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {X : Type*} [MeasurableSpace X]

/-- Restrict a square-integrable function to a measurable subset with its induced measure. -/
def restrictL2ToSubtype (μ : Measure X) (K : Set X) (hK : MeasurableSet K) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.comap (Subtype.val : K → X)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (Subtype.val : K → X)
    (measurePreserving_subtype_coe hK)).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
        (by simpa only [one_smul] using (Measure.restrict_le_self : μ.restrict K ≤ μ)))

/-- The bounded restriction map agrees almost everywhere with pointwise restriction. -/
theorem coeFn_restrictL2ToSubtype (μ : Measure X) (K : Set X) (hK : MeasurableSet K)
    (f : Lp ℝ 2 μ) :
    restrictL2ToSubtype μ K hK f =ᵐ[μ.comap (Subtype.val : K → X)] (fun x => f x.val) := by
  let R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict K) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa only [one_smul] using (Measure.restrict_le_self : μ.restrict K ≤ μ))
  have hm := measurePreserving_subtype_coe (μa := μ) hK
  have hR : R f =ᵐ[μ.restrict K] f := Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
  exact (Lp.coeFn_compMeasurePreserving (R f) hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp hR)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace X] [BorelSpace X]

/-- A compact restriction with full support gives a local uniform bound for representatives. -/
theorem exists_bound_continuous_representatives_on_compact (μ : Measure X) (K : Set X)
    (hK : MeasurableSet K) [CompactSpace K]
    [IsFiniteMeasure (μ.comap (Subtype.val : K → X))]
    [(μ.comap (Subtype.val : K → X)).IsOpenPosMeasure]
    (B : H →L[ℝ] Lp ℝ 2 μ) (u : H → X → ℝ)
    (hu : ∀ f, ContinuousOn (u f) K) (hae : ∀ f, B f =ᵐ[μ] u f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f x, x ∈ K → ‖u f x‖ ≤ C * ‖f‖ := by
  have hlocal : ∀ f, (restrictL2ToSubtype μ K hK).comp B f =ᵐ[μ.comap (Subtype.val : K → X)]
      (fun x : K => u f x.val) := by
    intro f
    exact (coeFn_restrictL2ToSubtype μ K hK (B f)).trans
      ((ae_restrict_iff_subtype hK).mp (ae_restrict_of_ae (hae f)))
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_continuous_representatives
    (μ.comap (Subtype.val : K → X)) ((restrictL2ToSubtype μ K hK).comp B)
    (fun f (x : K) => u f x.val) (fun f => (hu f).domRestrict) hlocal
  exact ⟨C, hC, fun f x hx => hbound f ⟨x, hx⟩⟩

end HeatKernel
