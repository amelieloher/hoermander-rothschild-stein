-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WeakRegularity
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A continuous representative has no support outside the
closed support of its almost-everywhere equivalent input
(BB p. 266). -/
theorem tsupport_continuousRepresentative_subset
    {u f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (he : u =ᵐ[volume] f) :
    tsupport f ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hxu
  let U := (tsupport u)ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  have hz : f =ᵐ[volume.restrict U] 0 := by
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hU.measurableSet] with y hy hyU
    change f y = 0
    rw [← hy]
    exact image_eq_zero_of_notMem_tsupport hyU
  have hfx := Measure.eqOn_open_of_ae_eq hz hU hf.continuousOn continuousOn_const hxu
  exact hx hfx

/-- The local weak regularity theorem gives a smooth compact correction
representative when the complete error equation L omega = g is supplied.
Pointwise equality away from zero follows from continuity there; the
regularity result applies to functions (BB p. 266). -/
theorem StandingHypotheses.exists_smoothCompact_correction
    (H : StandingHypotheses G q) (g ω : (Fin N → ℝ) → ℝ)
    (hω : Integrable ω) (hs : HasCompactSupport ω)
    (hc : ContinuousOn ω ({(0 : Fin N → ℝ)}ᶜ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (heq : ∀ φ : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, ω x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x, g x * φ x) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      ω =ᵐ[volume] f ∧ EqOn ω f ({(0 : Fin N → ℝ)}ᶜ) := by
  obtain ⟨f, hf, he⟩ := H.exists_smooth_globalRepresentative G g ω hω.locallyIntegrable hg heq
  have ht := tsupport_continuousRepresentative_subset hf.continuous he
  refine ⟨f, hf, hs.of_isClosed_subset isClosed_closure ht, he, ?_⟩
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae he) isOpen_compl_singleton hc hf.continuous.continuousOn

end RothschildStein.H1
