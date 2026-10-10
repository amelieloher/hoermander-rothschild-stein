-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.WeakLift
public import HeatKernel.Form.GraphForm
import Mathlib.Tactic.Linarith

/-!
# Strong L² limits with bounded horizontal energy

Uniformly bounded function norms and horizontal gradients give a bounded sequence in the
Hilbert graph. Its strong L² limit belongs to the energy domain and retains the gradient bound.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

private theorem le_add_of_sq_eq {a b c A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (haA : a ≤ A) (hbB : b ≤ B)
    (h : c ^ 2 = a ^ 2 + b ^ 2) : c ≤ A + B := by
  have hsa := (sq_le_sq₀ ha hA).mpr haA
  have hsb := (sq_le_sq₀ hb hB).mpr hbB
  nlinarith [mul_nonneg hA hB]

/-- Bounds for the function and gradient control the graph norm. -/
theorem energyGraph_norm_le_add_of_bounds {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u : energyGraph U X)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ‖energyInclusion U X u‖ ≤ A) (hg : ‖energyGradient U X u‖ ≤ B) :
    ‖u‖ ≤ A + B := by
  have h := energyGraph_norm_sq U X u
  rw [← PiLp.norm_sq_eq_of_L2] at h
  exact le_add_of_sq_eq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hA hB hf hg h

/-- Strong L² convergence and uniform function and gradient bounds produce an energy-domain
limit with the same gradient bound. -/
theorem exists_energyGraph_limit_of_bounds {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (u : ℕ → energyGraph U X) {f : SpatialL2 U} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ n, ‖energyInclusion U X (u n)‖ ≤ A)
    (hg : ∀ n, ‖energyGradient U X (u n)‖ ≤ B)
    (ht : Tendsto (fun n => energyInclusion U X (u n)) atTop (𝓝 f)) :
    ∃ z : energyGraph U X, energyInclusion U X z = f ∧
      ‖energyGradient U X z‖ ≤ B := by
  have hu := fun n => energyGraph_norm_le_add_of_bounds U X (u n) hA hB (hf n) (hg n)
  let : InnerProductSpace ℝ (energyGraph U X) :=
    { (inferInstance : InnerProductSpace ℝ (energyGraph U X)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (energyGraph U X)) }
  let : InnerProductSpace ℝ (SpatialL2 U) :=
    { (inferInstance : InnerProductSpace ℝ (SpatialL2 U)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (SpatialL2 U)) }
  obtain ⟨z, hz, _, hzg⟩ := exists_lift_of_tendsto_of_bounded
    (E := energyGraph U X) (H := SpatialL2 U)
    (K := PiLp 2 (fun _ : Fin q => SpatialL2 U))
    (energyInclusion U X) (energyGradient U X) u hu hg ht
  exact ⟨z, hz, hzg⟩

end HeatKernel
