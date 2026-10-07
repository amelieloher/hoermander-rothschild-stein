-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TruncationDilation
public import RothschildStein.Definitions.HomogeneousGroup.HasPrincipalValue
public import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter
open scoped Topology
variable {N : ℕ} (G : HomogeneousGroup N)

private theorem tendsto_positive_scale {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => t * ε) (𝓝[>] 0) (𝓝[>] 0) := by
  have h : Tendsto (fun ε : ℝ => t * ε)
      (comap (fun ε : ℝ => t * ε) (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
  simpa only [comap_mulLeft_nhdsGT_zero ht] using h

/-- Dilation preserves both existence and value of the fixed-gauge PV,
with the exact positive-truncation integrability clauses (BB pp. 356–357). -/
theorem hasPrincipalValue_dilation_iff
    {ν k : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hk : ∀ t : ℝ, 0 < t → ∀ w : Fin N → ℝ, w ≠ 0 →
      k (G.dilate t w) = t ^ (-(G.homogeneousDimension : ℝ)) * k w)
    (u : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) {t : ℝ} (ht : 0 < t) (value : ℝ) :
    G.HasPrincipalValue ν k (fun y => u (G.dilate t y)) x value ↔
      G.HasPrincipalValue ν k u (G.dilate t x) value := by
  have hdata {ε : ℝ} (hε : 0 < ε) :=
    principalValue_truncation_dilation_data G hν hk u x ht hε
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ε hε
      have hεt : 0 < t⁻¹ * ε := mul_pos (inv_pos.mpr ht) hε
      have hi := (hdata hεt).2.mp (h.1 _ hεt)
      simpa only [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] using hi
    · have hl := h.2.comp (tendsto_positive_scale (inv_pos.mpr ht))
      apply hl.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have heq := (hdata (mul_pos (inv_pos.mpr ht) hε)).1
      simpa only [Function.comp_def, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] using heq
  · intro h
    refine ⟨?_, ?_⟩
    · intro ε hε
      exact (hdata hε).2.mpr (h.1 _ (mul_pos ht hε))
    · have hl := h.2.comp (tendsto_positive_scale ht)
      apply hl.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hdata hε).1.symm

end RothschildStein.H3
