-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GaugeChartMass
public import RothschildStein.P1.FamilyChartIntegrability

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

/-- Actual positive-type principal families have one finite
absolute row-mass bound on the compact endpoint patch. The value at the
pole is arbitrary and is removed only on a null singleton. -/
theorem LiftedChart.exists_family_patch_mass_bound
    (C : LiftedChart w s Ω hΩ X x₀ m)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (d : ℤ) (hd : -(C.G.homogeneousDimension : ℤ) < d)
    (hbound : HasWeightedBounds C.G d Ψ)
    (L : Set (Fin (n + m) → ℝ)) (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ξ ∈ L,
      (∫⁻ η in L, ‖Ψ ξ η (C.Θ η ξ)‖ₑ) ≤ A := by
  let rsFamilyMassFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  obtain ⟨R, hR⟩ := C.exists_gauge_bound hL hLU
  obtain ⟨M, hM, hb⟩ := hbound L hL R
  obtain ⟨A, hA, ha⟩ := C.exists_gauge_patch_mass_bound d hd L hL hLU
  refine ⟨ENNReal.ofReal M * A, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA, ?_⟩
  intro ξ hξ
  calc
    _ ≤ ∫⁻ η in L, ENNReal.ofReal M *
        ENNReal.ofReal (kgauge C.G (C.Θ η ξ) ^ d) := by
      apply setLIntegral_mono_ae' hL.measurableSet
      filter_upwards [volume.ae_ne ξ] with η hη
      intro hηL
      have hu : C.Θ η ξ ≠ 0 :=
        (C.theta_eq_zero_iff (hLU hηL) (hLU hξ)).not.mpr hη.symm
      have hs := (hb ξ hξ η hηL (C.Θ η ξ) hu (hR η hηL ξ hξ)).1
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal M * ∫⁻ η in L,
        ENNReal.ofReal (kgauge C.G (C.Θ η ξ) ^ d) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M * A := mul_le_mul_right (ha ξ hξ) _

end RothschildStein.P1
