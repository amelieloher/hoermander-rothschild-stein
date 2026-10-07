-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WeakEquationDictionary
public import Hormander.Interface

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The local weak regularity theorem supplies smooth representatives for the
standing group's L1-local weak solutions on every open set. It applies to
function inputs and does not assert hypoellipticity for arbitrary
distributions (BB p. 256). -/
theorem StandingHypotheses.exists_smooth_weakRepresentative
    (H : StandingHypotheses G q) {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (g u : (Fin N → ℝ) → ℝ) (hu : LocallyIntegrableOn u U volume)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (heq : ∀ φ : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, u x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x in U, g x * φ x) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f U ∧
      u =ᵐ[volume.restrict U] f := by
  apply Hormander.Interface.exists_smooth_aeRepresentative hU H.fields 0 g u
    (H.fields_contDiffOn G U) (H.spansOn G U) contDiffOn_const
  exact (H.hasWeakHormanderEquation_iff G U g u).mpr ⟨hu, hg, heq⟩

/-- Global weak regularity for locally integrable solutions of the standing
operator. It applies once the local distribution is represented by a
function. -/
theorem StandingHypotheses.exists_smooth_globalRepresentative
    (H : StandingHypotheses G q) (g u : (Fin N → ℝ) → ℝ)
    (hu : LocallyIntegrable u) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (heq : ∀ φ : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x, g x * φ x) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ u =ᵐ[volume] f := by
  have hloc : LocallyIntegrableOn u (univ : Set (Fin N → ℝ)) volume :=
    locallyIntegrableOn_univ.mpr hu
  obtain ⟨f, hf, he⟩ := H.exists_smooth_weakRepresentative G isOpen_univ g u hloc hg.contDiffOn
    (fun φ hφ hc _ => by simpa only [setIntegral_univ] using heq φ hφ hc)
  exact ⟨f, contDiffOn_univ.mp hf, by simpa only [Measure.restrict_univ] using he⟩

end RothschildStein.H1
