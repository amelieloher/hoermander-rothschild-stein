-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierSubstitution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Dilation depends continuously on its real parameter, including
parameter zero (BB p. 122; polynomial continuity). -/
theorem continuous_dilate_parameter (z : Fin N → ℝ) :
    Continuous (fun ε : ℝ => G.dilate ε z) := by
  apply continuous_pi
  intro j
  exact (continuous_id.pow (G.weight j)).mul continuous_const

/-- The translated argument tends to x under small dilations
(BB Prop 3.48 proof, p. 122). -/
theorem tendsto_dilated_inv_translate (z x : Fin N → ℝ) :
    Tendsto (fun ε : ℝ => G.mul (G.inv (G.dilate ε z)) x) (𝓝 0) (𝓝 x) := by
  have H := ((continuous_mul G).comp
    (((continuous_inv G).comp (continuous_dilate_parameter G z)).prodMk (continuous_const (y := x)))).tendsto 0
  change Tendsto (fun ε : ℝ => G.mul (G.inv (G.dilate ε z)) x)
    (𝓝 0) (𝓝 (G.mul (G.inv (G.dilate 0 z)) x)) at H
  simpa only [zero_dilate, inv_zero, zero_mul] using H

/-- Regularization tends pointwise to every bounded continuous
input as ε tends to zero through positive values (BB p. 122). -/
theorem tendsto_groupRegularize_pointwise {ν : HomogeneousNorm G}
    (φ : GroupMollifier G ν) {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : Fin N → ℝ) :
    Tendsto (fun ε : ℝ => groupRegularize G φ f ε x) (𝓝[>] 0) (𝓝 (f x)) := by
  have hφ : Integrable φ := φ.smooth.continuous.integrable_of_hasCompactSupport φ.compact
  have hm (ε : ℝ) : AEStronglyMeasurable
      (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
    (φ.smooth.continuous.mul (hf.comp ((continuous_mul G).comp
      (((continuous_inv G).comp (continuous_dilate G ε)).prodMk continuous_const)))).aestronglyMeasurable
  have hb (ε : ℝ) : ∀ᵐ z ∂volume,
      ‖φ z * f (G.mul (G.inv (G.dilate ε z)) x)‖ ≤ ‖φ z‖ * C :=
    Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  have ht : ∀ᵐ z ∂volume, Tendsto
      (fun ε : ℝ => φ z * f (G.mul (G.inv (G.dilate ε z)) x))
      (𝓝[>] 0) (𝓝 (φ z * f x)) := Eventually.of_forall fun z =>
    tendsto_const_nhds.mul ((hf.tendsto x).comp
      ((tendsto_dilated_inv_translate G z x).mono_left nhdsWithin_le_nhds))
  have H := tendsto_integral_filter_of_dominated_convergence (fun z => ‖φ z‖ * C)
    (Eventually.of_forall hm) (Eventually.of_forall hb) (hφ.norm.mul_const C) ht
  have he : (∫ z, φ z * f x) = f x := by
    rw [integral_mul_const, φ.integral_eq_one, one_mul]
  rw [he] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (groupRegularize_eq_integral G φ f hε x).symm

end RothschildStein.G2
