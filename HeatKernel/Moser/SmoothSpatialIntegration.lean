-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.SmoothLocalEnergy
public import RothschildStein.S.WeakDeriv
public import RothschildStein.G2.InvariantIntegration

/-!
# Spatial integration by parts on space-time

The integration-by-parts identity for a left-invariant field extends to smooth
space-time functions by Fubini. Compact support of the test function removes
all spatial boundary terms.
-/

@[expose] public section

open MeasureTheory Set Topology RothschildStein

namespace HeatKernel

/-- Spatial sections of compact spacetime tests have compact support. -/
theorem hasCompactSupport_spaceSection {E : Type*} [TopologicalSpace E]
    {φ : ℝ × E → ℝ} (hc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (fun x => φ (t, x)) := by
  have he : IsClosedEmbedding (Prod.mk t : E → ℝ × E) := by
    refine ⟨isEmbedding_prodMkRight t, ?_⟩
    have hr : range (Prod.mk t : E → ℝ × E) = Prod.fst ⁻¹' {t} := by
      ext z
      simp only [mem_range, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl⟩
        rfl
      · intro hz
        exact ⟨z.2, Prod.ext hz.symm rfl⟩
    rw [hr]
    exact isClosed_singleton.preimage continuous_fst
  exact hc.comp_isClosedEmbedding he

/-- Evaluating the differential of a compact test on a variable vector preserves compact support. -/
theorem hasCompactSupport_fderiv_apply_variable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : E → ℝ} (hc : HasCompactSupport φ) (V : E → E) :
    HasCompactSupport (fun z => fderiv ℝ φ z (V z)) := by
  apply (hc.fderiv ℝ).mono
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro he
  exact hz (by simp [he])

/-- Evaluating the differential on a variable vector does not enlarge the test support. -/
theorem tsupport_fderiv_apply_variable_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ : E → ℝ) (V : E → E) :
    tsupport (fun z => fderiv ℝ φ z (V z)) ⊆ tsupport φ := by
  apply closure_minimal ?_ (isClosed_tsupport φ)
  intro z hz
  apply support_fderiv_subset ℝ
  simp only [Function.mem_support] at hz ⊢
  intro he
  exact hz (by simp [he])

end HeatKernel
