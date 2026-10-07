-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ChartMassBound
public import RothschildStein.P1.GaugeChartIntegrability
public import RothschildStein.G2.MeasureConsequences

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A positive-type gauge power has uniformly finite chart mass
on a fixed compact endpoint patch. -/
theorem LiftedChart.exists_gauge_patch_mass_bound
    (C : LiftedChart w s Ω hΩ X x₀ m) (d : ℤ)
    (hd : -(C.G.homogeneousDimension : ℤ) < d)
    (L : Set (Fin (n + m) → ℝ)) (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ξ ∈ L,
      (∫⁻ η in L, ENNReal.ofReal (kgauge C.G (C.Θ η ξ) ^ d)) ≤ A := by
  obtain ⟨B, _, hb⟩ := C.exists_inverseJacobian_bound L hL hLU
  obtain ⟨R, hR⟩ := C.exists_gauge_bound hL hLU
  let R₁ := max R 1
  have hR₁ : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let I := ∫⁻ u in {u : Fin (n + m) → ℝ | kgauge C.G u ≤ R₁},
    ENNReal.ofReal (kgauge C.G u ^ d)
  have hpower : -(d : ℝ) < C.G.homogeneousDimension := by
    have he : -(C.G.homogeneousDimension : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hI : I ≠ ⊤ := by
    simpa only [I, kgauge, neg_neg, Real.rpow_intCast] using
      (G2.power_lintegral_near_finite_iff (G2.isHomogeneousGauge_max C.G)
        (-(d : ℝ)) hR₁).mpr hpower
  refine ⟨ENNReal.ofReal B * I, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI, ?_⟩
  intro ξ hξ
  calc
    _ ≤ ENNReal.ofReal B * ∫⁻ u in (fun η => C.Θ η ξ) '' L,
        ENNReal.ofReal (kgauge C.G u ^ d) :=
      C.lintegral_comp_theta_le ξ (hLU hξ) L hL.measurableSet hLU B (hb ξ hξ) _
    _ ≤ ENNReal.ofReal B * I := by
      apply mul_le_mul_right
      apply lintegral_mono_set
      rintro u ⟨η, hη, rfl⟩
      exact (hR η hη ξ hξ).trans (le_max_left _ _)

end RothschildStein.P1
