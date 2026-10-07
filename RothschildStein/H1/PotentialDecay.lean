-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PotentialBound
public import RothschildStein.H1.GaugeDecay
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The fundamental potential tends to zero at Euclidean
infinity, with no symmetry hypothesis on the homogeneous norm
(BB Theorem 6.20(3), printed pp. 270–271). -/
theorem fundamentalPotential_decay (ν : G2.HomogeneousNorm G)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) {Γ φ : (Fin N → ℝ) → ℝ}
    (hcΓ : ContinuousOn Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hhΓ : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      Γ (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * Γ x)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ ‖x‖ →
      ‖∫ y, Γ (G.mul (G.inv y) x) * φ y‖ ≤ ε := by
  obtain ⟨C, hC, hb⟩ := homogeneous_bound G ν _ hcΓ hhΓ
  obtain ⟨R, hR⟩ := hcφ.isCompact.bddAbove_image ν.gauge.1.continuousOn
  have hs : ∀ y, φ y ≠ 0 → ν y ≤ R :=
    fun y hy => hR ⟨y, subset_closure hy, rfl⟩
  apply decay_of_gauge_power_bound G ν (a := 2 - (G.homogeneousDimension : ℝ))
    (C := C * (2 * ν.c) ^ (-(2 - (G.homogeneousDimension : ℝ))) * ∫ y, |φ y|)
    (A := max 1 (2 * ν.c * R)) (by linarith)
  intro x hx
  have hn : 1 ≤ ν x := (le_max_left _ _).trans hx
  have hx0 : x ≠ 0 := by
    intro he
    have hz := (ν.gauge.2.2.1 x).mpr he
    linarith
  have h := fundamentalPotential_bound G ν (by linarith : 2 - (G.homogeneousDimension : ℝ) ≤ 0)
    hC.le hb (hφ.integrable_of_hasCompactSupport hcφ) hs hx0 ((le_max_right _ _).trans hx)
  convert h using 1
  ring

end RothschildStein.H1
