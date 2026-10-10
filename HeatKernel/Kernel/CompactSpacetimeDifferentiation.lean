-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactSpacetimeContinuity
public import HeatKernel.Kernel.DominatedScalarSlopes

/-! # L² differentiation of compact spacetime slices

A continuous compact scalar time derivative controls the difference
quotients uniformly in space. The scalar time derivative is therefore
also the derivative of the L²-valued curve of spatial slices.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- A continuous compact scalar time derivative differentiates the L²-valued slice curve. -/
theorem hasDerivAt_toLp_spatial_slices {n : ℕ}
    (φ d : ℝ × (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hd : Continuous d)
    (hcφ : HasCompactSupport φ) (hcd : HasCompactSupport d)
    (hderiv : ∀ t x, HasDerivAt (fun s => φ (s, x)) (d (t, x)) t) (a : ℝ) :
    HasDerivAt (fun t => (memLp_two_spatial_slice φ hφ hcφ t).toLp
      (fun x => φ (t, x)))
      ((memLp_two_spatial_slice d hd hcd a).toLp (fun x => d (a, x))) a := by
  let K : Set (Fin n → ℝ) := (Prod.snd '' tsupport φ) ∪ (Prod.snd '' tsupport d)
  have hK : IsCompact K := (hcφ.image continuous_snd).union (hcd.image continuous_snd)
  obtain ⟨B, hB⟩ := hcd.exists_bound_of_continuousOn hd.continuousOn
  let C : ℝ := max B 0
  have hnorm (z : ℝ × (Fin n → ℝ)) : ‖d z‖ ≤ C := by
    by_cases hz : z ∈ tsupport d
    · exact (hB z hz).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  let g : (Fin n → ℝ) → ℝ := K.indicator (fun _ => 2 * C)
  have hg : MemLp g 2 volume :=
    memLp_indicator_const 2 hK.measurableSet (2 * C) (Or.inr hK.measure_ne_top)
  apply hasDerivAt_toLp_two_of_dominated_slopes (fun t x => φ (t, x))
    (memLp_two_spatial_slice φ hφ hcφ) (memLp_two_spatial_slice d hd hcd a) hg
    (Eventually.of_forall (hderiv a))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t ≠ a := by simpa using ht
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ K
    · change ‖(t - a)⁻¹ * (φ (t, x) - φ (a, x)) - d (a, x)‖ ≤
        K.indicator (fun _ => 2 * C) x
      rw [Set.indicator_of_mem hx]
      exact norm_slope_error_le_of_derivative_bound (fun s => φ (s, x))
        (fun s => d (s, x)) (fun s => hderiv s x) (fun s => hnorm (s, x)) hne
    · have hzeroφ (s : ℝ) : φ (s, x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hz => hx (Or.inl ⟨(s, x), hz, rfl⟩))
      have hzerod : d (a, x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hz => hx (Or.inr ⟨(a, x), hz, rfl⟩))
      change ‖(t - a)⁻¹ * (φ (t, x) - φ (a, x)) - d (a, x)‖ ≤
        K.indicator (fun _ => 2 * C) x
      rw [hzeroφ t, hzeroφ a, hzerod, sub_self, mul_zero, sub_self, norm_zero,
        Set.indicator_of_notMem hx]

end HeatKernel
