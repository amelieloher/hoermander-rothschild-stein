-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CompactDomainBallEquality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.L1

/-- Small-radius ball equality identifies the underlying extended
distances wherever the smaller-domain distance is below the threshold. -/
theorem ennreal_eq_of_small_ball_comparison {a b : ℝ≥0∞} {R : ℝ}
    (hab : a ≤ b) (hb : b < ENNReal.ofReal R)
    (hball : ∀ r : ℝ, 0 < r → r ≤ R →
      (a < ENNReal.ofReal r ↔ b < ENNReal.ofReal r)) : a = b := by
  apply le_antisymm hab
  by_contra h
  have hlt : a < b := lt_of_not_ge h
  obtain ⟨r,_hr,har,hrb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le har)
  have hrR : r ≤ R := ((ENNReal.ofReal_lt_ofReal_iff'.mp (hrb.trans hb)).1).le
  exact (not_lt_of_ge hrb.le) ((hball r hrpos hrR).mp har)

/-- Actual compact-domain ball equality gives equality of the original
ambient and patch control distances at every sufficiently close pair. -/
theorem exists_compact_controlDistance_domain_equality {a n : ℕ}
    {U K : Set (Fin n → ℝ)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U) (w : Fin a → ℕ+) :
    ∃ R : ℝ, 0 < R ∧ ∀ Ω : Set (Fin n → ℝ), U ⊆ Ω →
      ∀ x ∈ K, ∀ y, controlDistance U w X x y < ENNReal.ofReal R →
        controlDistance Ω w X x y = controlDistance U w X x y := by
  obtain ⟨R,hR,_hR1,he⟩ := exists_compact_controlBall_domain_equality hU hK hKU X hX w
  refine ⟨R,hR,?_⟩
  intro Ω hUΩ x hx y hxy
  apply ennreal_eq_of_small_ball_comparison (G1.controlDistance_mono_domain w X hUΩ x y) hxy
  intro r hr hrR
  have hh := congrArg (fun S => y ∈ S) (he Ω hUΩ x hx r hr hrR)
  exact iff_of_eq hh
end RothschildStein.L1
