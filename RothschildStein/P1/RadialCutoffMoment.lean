-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellRadialWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ}

/-- A radial cutoff equal to one near zero has
zero critical cutoff moment. The proof uses only shell cancellation;
no integral of the bare kernel over a ball is asserted. -/
theorem integral_radialCutoffMoment_zero (G : HomogeneousGroup N)
    {ν κ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hκ : ContinuousOn κ {(0 : Fin N → ℝ)}ᶜ)
    (hc : H1.HasVanishingShellIntegrals ν κ)
    (Φ : ℝ → ℝ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hΦ : ContinuousOn Φ (Icc r R)) (hone : ∀ t : ℝ, t < r → Φ t = 1) :
    (∫ u in {u | ν u ≤ R}, κ u * (1 - Φ (ν u))) = 0 := by
  have hs : H1.gaugeShell ν r R ⊆ {u | ν u ≤ R} := fun u hu => hu.2
  have hm : MeasurableSet {u | ν u ≤ R} :=
    measurableSet_le hν.1.measurable measurable_const
  have he := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (μ := volume) (f := fun u => κ u * (1 - Φ (ν u))) hm hs
    (fun u hu => by
      have hl : ν u < r := by
        by_contra hn
        exact hu.2 ⟨le_of_not_gt hn, hu.1⟩
      rw [hone _ hl, sub_self, mul_zero])
  rw [he]
  exact H1.integral_gaugeShell_radialWeight_zero G hν hκ hc hr hrR
    (continuousOn_const.sub hΦ)

end RothschildStein.P1
