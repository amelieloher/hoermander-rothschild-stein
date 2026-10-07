-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.NumericalControlledCurveBuffer

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.Geometry

/-- Numerical first exit identifies ambient and buffered distances at
small ambient distance, uniformly across all bounded coefficient families.
BB Theorem 9.6, p. 403, and Lemma 9.57, pp. 459–460,
with the ambient-domain buffer retained. -/
theorem exists_numerical_controlDistance_domain_equality {m n : ℕ}
    (R P : ℝ) (hR : 0 < R) :
    ∃ η : ℝ, 0 < η ∧ ∀ (Ω V : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
      (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin n → ℝ),
      V ⊆ Ω → closedBall z R ⊆ V →
      (∀ i y, y ∈ closedBall z R → ‖Z i y‖ ≤ P) →
      ∀ x ∈ closedBall z (R/2), ∀ y,
      controlDistance Ω w Z x y < ENNReal.ofReal η →
      controlDistance Ω w Z x y = controlDistance V w Z x y := by
  obtain ⟨η, hη, _hη1, hstay⟩ := G4.exists_numerical_controlled_curve_buffer
    (m := m) (n := n) R P hR
  refine ⟨η, hη, ?_⟩
  intro Ω V w Z z hVΩ hball hbound x hx y hd
  apply le_antisymm (G1.controlDistance_mono_domain w Z hVΩ x y)
  by_contra h
  have hlt : controlDistance Ω w Z x y < controlDistance V w Z x y := lt_of_not_ge h
  obtain ⟨r, _hr, har, hrb⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_min hlt hd)
  obtain ⟨δ, _hδ, hδr, γ, hγ, hzero, hone⟩ := G1.exists_controlledCurve_of_controlDistance_lt har
  have hrη : r < η := (ENNReal.ofReal_lt_ofReal_iff'.mp (hrb.trans_le (min_le_right _ _))).1
  have hmap := hstay Ω w Z z hbound δ (hδr.trans hrη) γ hγ (by simpa only [hzero] using hx)
  have hv : isControlledCurve V w Z δ γ :=
    ⟨hγ.1, hγ.2.1, fun t ht => hball (hmap ht), hγ.2.2.2⟩
  have hcost := G1.controlDistance_le_of_curve hv
  rw [hzero, hone] at hcost
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le har)
  have hδcost := (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hδr
  exact (not_lt_of_ge hcost) (hδcost.trans (hrb.trans_le (min_le_left _ _)))

end RothschildStein.Geometry
