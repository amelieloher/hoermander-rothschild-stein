-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorPairing
public import RothschildStein.H1.WeakRegularity
public import RothschildStein.H1.StandingComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A locally integrable weak null solution that is continuous away
from zero and tends to zero at infinity vanishes almost everywhere
(BB Theorem 6.18, p. 271). -/
theorem StandingHypotheses.weak_null_decay_ae_zero
    (H : StandingHypotheses G q) {u : (Fin N → ℝ) → ℝ} (hu : LocallyIntegrable u)
    (hc : ContinuousOn u ({(0 : Fin N → ℝ)}ᶜ))
    (hnull : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, u x * sumSquaresWithDriftTranspose H.fields φ x) = 0)
    (hdecay : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → ‖u x‖ ≤ ε) :
    u =ᵐ[volume] 0 := by
  obtain ⟨f, hf, hef⟩ := H.exists_smooth_globalRepresentative G 0 u hu contDiff_const
    (fun φ hφ hs => by simpa only [Pi.zero_apply, zero_mul, integral_zero] using hnull φ hφ hs)
  have hLf : sumSquaresWithDrift H.fields f = (fun _ => (0 : ℝ)) := by
    apply H.operator_eq_of_weak_pairing G hf continuous_const
    intro φ hφ hs
    have he : (∫ x, f x * sumSquaresWithDriftTranspose H.fields φ x) =
        ∫ x, u x * sumSquaresWithDriftTranspose H.fields φ x := by
      apply integral_congr_ae
      filter_upwards [hef] with x hx
      rw [hx]
    simpa only [Pi.zero_apply, zero_mul, integral_zero] using he.trans (hnull φ hφ hs)
  have he : EqOn u f ({(0 : Fin N → ℝ)}ᶜ) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hef) isOpen_compl_singleton hc
      hf.continuous.continuousOn
  have hdf : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ ‖x‖ → ‖f x‖ ≤ ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := hdecay ε hε
    refine ⟨max R 1, fun x hx => ?_⟩
    have hx0 : x ≠ 0 := by
      intro hz
      have hn := (le_max_right R 1).trans hx
      rw [hz, norm_zero] at hn
      linarith
    rw [← he hx0]
    exact hR x ((le_max_left _ _).trans hx)
  have hfields : driftCoefficientFields G H 1 = H.fields := by
    funext i
    simp only [driftCoefficientFields, one_smul]
    split_ifs with hi
    · rw [hi]
    · rfl
  have hz := H.liouville G 1 (hf.of_le (by simp))
    (fun x => by rw [hfields, hLf]) hdf
  exact hef.trans (Filter.EventuallyEq.of_eq hz)

end RothschildStein.H1
