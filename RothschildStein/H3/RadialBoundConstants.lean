-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GaugeWordBounds
public import RothschildStein.H3.ProfileDerivatives
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.wordWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The fixed Sobolev drift weights agree with H1's differential words. -/
theorem drift_wordWeight_eq {q : ℕ} (I : List (Fin (q+1))) :
    wordWeight driftWeight I = H1.differentialWordWeight I := by
  unfold wordWeight H1.differentialWordWeight
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [driftWeight]
  split_ifs <;> rfl

/-- Profile constants for all positive derivative orders, independent
 of both radii. The unused order-zero constant may be zero. -/
theorem exists_profile_word_constants :
    ∃ κ : ℕ → ℝ, (∀ j, 0 ≤ κ j) ∧ ∀ j, 0 < j →
      ∀ t s : ℝ, t < s → ∀ x, |iteratedDeriv j (quasiballProfile t s) x| ≤
        κ j*(2/(s-t))^j := by
  classical
  have he : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ (0 < j →
      ∀ t s : ℝ, t < s → ∀ x, |iteratedDeriv j (quasiballProfile t s) x| ≤ c*(2/(s-t))^j) := by
    intro j
    by_cases hj : 0 < j
    · obtain ⟨c,hc,hb⟩ := exists_quasiballProfile_derivative_bound hj
      exact ⟨c,hc,fun _ => hb⟩
    · exact ⟨0,le_rfl,fun h => (hj h).elim⟩
  choose κ hκ hb using he
  exact ⟨κ,hκ,hb⟩

/-- Gauge constants for every word, obtained from the proved H1
 homogeneity and H3 sphere bounds, with the fixed Sobolev weights. -/
theorem exists_gauge_word_constants {n q : ℕ} (G : HomogeneousGroup n)
    (H : H1.StandingHypotheses G q) (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ M : List (Fin (q+1)) → ℝ, (∀ I, 0 ≤ M I) ∧ ∀ I x, x ≠ 0 →
      |wordDerivative H.fields I ν x| ≤ M I*(ν x)^(1-(wordWeight driftWeight I : ℝ)) := by
  classical
  choose M hM hb using (fun I => gauge_wordDerivative_bound G H ν hν I)
  refine ⟨M,hM,?_⟩
  intro I x hx
  simpa only [drift_wordWeight_eq] using hb I x hx

end RothschildStein.H3
