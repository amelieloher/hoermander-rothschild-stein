-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExteriorWordBounds
public import RothschildStein.H3.RightFieldHomogeneity
public import RothschildStein.H1.Standing
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A finite frame containing the prescribed left fields and
 their right partners, with the same weights in both blocks. -/
def mixedInvariantFields (H : H1.StandingHypotheses G q) :
    Fin ((q + 1) + (q + 1)) → (Fin N → ℝ) → (Fin N → ℝ) :=
  Fin.addCases H.fields (fun i => G2.rightField G (H.fields i 0))

/-- The duplicated drift weights for the mixed frame. -/
def mixedInvariantWeights (q : ℕ) : Fin ((q + 1) + (q + 1)) → ℕ+ :=
  Fin.addCases driftWeight driftWeight

/-- Both blocks of the actual mixed frame are smooth. -/
theorem mixedInvariantFields_smooth (H : H1.StandingHypotheses G q)
    (i : Fin ((q + 1) + (q + 1))) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedInvariantFields G H i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [mixedInvariantFields, Fin.addCases_left] using H.fields_smooth G j
  · simpa only [mixedInvariantFields, Fin.addCases_right] using G2.contDiff_rightField G (H.fields j 0)

/-- Both blocks have the prescribed weights, including drift. -/
theorem mixedInvariantFields_homogeneous (H : H1.StandingHypotheses G q)
    (i : Fin ((q + 1) + (q + 1))) :
    G2.IsHomogeneousField G (mixedInvariantFields G H i)
      (((mixedInvariantWeights q i : ℕ) : ℝ)) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [mixedInvariantFields, mixedInvariantWeights, Fin.addCases_left]
    by_cases hj : j = 0
    · simpa [driftWeight, hj] using H.homogeneous j
    · simpa [driftWeight, hj] using H.homogeneous j
  · simp only [mixedInvariantFields, mixedInvariantWeights, Fin.addCases_right]
    by_cases hj : j = 0
    · simpa [driftWeight, hj] using rightField_identity_value_homogeneous G (H.homogeneous j)
    · simpa [driftWeight, hj] using rightField_identity_value_homogeneous G (H.homogeneous j)

/-- far part. The actual left/right mixed words of the
exterior kernel have uniform scale bounds, one constant per word.
This includes left differentiation of the right sum-of-squares kernel. -/
theorem exists_mixed_exterior_word_bounds (H : H1.StandingHypotheses G q)
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hzero : ∀ t : ℝ, 1 ≤ t → φ t = 0)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {γ : ℝ} (hγ : γ ≤ 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x) :
    ∃ C : List (Fin ((q + 1) + (q + 1))) → ℝ, (∀ I, 0 ≤ C I) ∧
      ∀ I (ε : ℝ), 0 < ε → ∀ x,
        |wordDerivative (mixedInvariantFields G H) I (exteriorCutoffKernel ν φ F ε) x| ≤
          C I * ε ^ (γ - (wordWeight (mixedInvariantWeights q) I : ℝ)) := by
  classical
  have hdegree (I : List (Fin ((q + 1) + (q + 1)))) :
      γ - (wordWeight (mixedInvariantWeights q) I : ℝ) ≤ 0 := by
    have hw : (0 : ℝ) ≤ (wordWeight (mixedInvariantWeights q) I : ℝ) := by positivity
    linarith
  have hb (I : List (Fin ((q + 1) + (q + 1)))) :=
    exteriorCutoffKernel_word_bound (mixedInvariantWeights q) (mixedInvariantFields G H)
      (mixedInvariantFields_smooth G H) (mixedInvariantFields_homogeneous G H)
      hν hsν hφ hone hzero hF hhom I (hdegree I)
  exact ⟨fun I => (hb I).choose, fun I => (hb I).choose_spec.1,
    fun I => (hb I).choose_spec.2⟩

end RothschildStein.H3
