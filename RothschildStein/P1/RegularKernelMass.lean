-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularKernelIntegrability

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.P1

variable {N : ℕ}

private theorem row_mass_le_indicator
    (r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (C : ℝ) (K : Set (Fin N → ℝ))
    (hK : MeasurableSet K) (hbound : ∀ ξ η, ‖r ξ η‖ ≤ C)
    (hsupport : ∀ ξ η, η ∉ K → r ξ η = 0) (ξ : Fin N → ℝ) :
    (∫⁻ η, ‖r ξ η‖ₑ) ≤ ENNReal.ofReal C * volume K := by
  calc
    (∫⁻ η, ‖r ξ η‖ₑ) ≤ ∫⁻ η, K.indicator (fun _ => ENNReal.ofReal C) η := by
      apply lintegral_mono
      intro η
      by_cases hη : η ∈ K
      · simp only [Set.indicator_of_mem hη]
        simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
          ENNReal.ofReal_le_ofReal (hbound ξ η)
      · simp only [hsupport ξ η hη, enorm_zero, Set.indicator_of_notMem hη, le_refl]
    _ = ENNReal.ofReal C * volume K := by
      rw [lintegral_indicator hK, lintegral_const, Measure.restrict_apply_univ]

/-- Regular components have finite uniform row and column absolute masses.
These are the actual nonnegative integrals used by the Schur theorem. -/
theorem IsRegularKernel.exists_schur_bounds {F : KernelFrame N} {m : ℕ}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F m r) :
    ∃ A B : ℝ≥0∞, A ≠ ⊤ ∧ B ≠ ⊤ ∧
      (∀ ξ, (∫⁻ η, ‖r ξ η‖ₑ) ≤ A) ∧ (∀ η, (∫⁻ ξ, ‖r ξ η‖ₑ) ≤ B) := by
  obtain ⟨C, hC⟩ := hr.2.1.exists_bound_of_continuousOn hr.1.continuous.continuousOn
  have hbound : ∀ ξ η, ‖r ξ η‖ ≤ |C| := by
    intro ξ η
    by_cases h0 : r ξ η = 0
    · simp only [h0, norm_zero]
      exact abs_nonneg C
    · exact (hC (ξ, η) (subset_tsupport _ h0)).trans (le_abs_self C)
  let Krow := Prod.snd '' tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2)
  let Kcol := Prod.fst '' tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2)
  have hKr : IsCompact Krow := hr.2.1.image continuous_snd
  have hKc : IsCompact Kcol := hr.2.1.image continuous_fst
  refine ⟨ENNReal.ofReal |C| * volume Krow, ENNReal.ofReal |C| * volume Kcol,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKr.measure_lt_top.ne,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKc.measure_lt_top.ne, ?_, ?_⟩
  · apply row_mass_le_indicator r |C| Krow hKr.measurableSet hbound
    intro ξ η hη
    by_contra h0
    exact hη ⟨(ξ, η), subset_tsupport _ h0, rfl⟩
  · apply row_mass_le_indicator (fun η ξ => r ξ η) |C| Kcol hKc.measurableSet
      (fun η ξ => hbound ξ η)
    intro η ξ hξ
    by_contra h0
    exact hξ ⟨(ξ, η), subset_tsupport _ h0, rfl⟩

end RothschildStein.P1
