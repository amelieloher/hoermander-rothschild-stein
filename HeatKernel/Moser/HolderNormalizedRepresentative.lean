-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderRepresentativeModulus
import Mathlib.Tactic

/-! # Continuous extension with a radius-normalized Hölder modulus -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace HeatKernel

/-- A normalized Hölder bound on a full-measure set extends continuously with
exactly the same radius, oscillation scale and dimensionless constant. -/
theorem exists_continuous_representative_of_normalized_holder_bound
    {A : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
    (μ : Measure A) [μ.IsOpenPosMeasure] (u : A → ℝ) {s : Set A}
    {C a r W : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hr : 0 < r) (hW : 0 ≤ W)
    (hfull : ∀ᵐ x ∂μ, x ∈ s)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, |u x - u y| ≤ C * (dist x y / r) ^ a * W) :
    ∃ v : A → ℝ, Continuous v ∧ v =ᵐ[μ] u ∧
      ∀ x y, |v x - v y| ≤ C * (dist x y / r) ^ a * W := by
  let K : ℝ≥0 := ⟨C / r ^ a * W, by positivity⟩
  let b : ℝ≥0 := ⟨a, ha.le⟩
  have hfactor (d : ℝ) (hd : 0 ≤ d) :
      C * (d / r) ^ a * W = (K : ℝ) * d ^ (b : ℝ) := by
    change C * (d / r) ^ a * W = (C / r ^ a * W) * d ^ a
    rw [Real.div_rpow hd hr.le]
    ring
  have hu : HolderOnWith K b u s := by
    intro x hx y hy
    have hb := hbound x hx y hy
    rw [hfactor _ dist_nonneg] at hb
    have he := ENNReal.ofReal_le_ofReal hb
    simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_mul K.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg dist_nonneg b.coe_nonneg] using he
  obtain ⟨v, hv, he, hmod⟩ :=
    exists_continuous_representative_with_holder_modulus μ hfull
      (show 0 < b from ha) hu
  refine ⟨v, hv, he, ?_⟩
  intro x y
  rw [hfactor _ dist_nonneg]
  simpa only [Real.dist_eq] using hmod x y

end HeatKernel
