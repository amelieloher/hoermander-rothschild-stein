-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.MeasurableCurves
public import HeatKernel.Form.CoreGradientGraph
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.NormNum

/-!
# Measurability of weak-gradient curves

Jointly measurable scalar representatives give measurable curves in the Hilbert graph of the
weak gradient. The membership hypothesis concerns spatial weak derivatives only.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace HeatKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {N q : ℕ}
    {U : Opens (Fin N → ℝ)}

/-- The graph norm gives the same Bochner Lp class as componentwise spatial L² norms. -/
theorem memLp_GradientSpace_iff {v : α → GradientSpace U q} {p : ℝ≥0∞} :
    MemLp v p μ ↔ MemLp (fun a => (v a).fst) p μ ∧
      ∀ i, MemLp (fun a => (v a).snd i) p μ := by
  rw [← memLp_comp_continuousLinearEquiv_iff
    (WithLp.prodContinuousLinearEquiv 2 ℝ (SpatialL2 U)
      (PiLp 2 (fun _ : Fin q => SpatialL2 U))) v, memLp_prod_iff]
  change (MemLp (fun a => (v a).fst) p μ ∧ MemLp (fun a => (v a).snd) p μ) ↔ _
  apply and_congr_right
  intro _
  rw [← memLp_comp_continuousLinearEquiv_iff
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => SpatialL2 U))
      (fun a => (v a).snd), memLp_pi_iff]
  rfl

/-- Bochner Lp membership in the energy graph is equivalent to componentwise membership. -/
theorem memLp_energyGraph_iff {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {v : α → energyGraph U X} {p : ℝ≥0∞} :
    MemLp v p μ ↔ MemLp (fun a => (v a : GradientSpace U q).fst) p μ ∧
      ∀ i, MemLp (fun a => (v a : GradientSpace U q).snd i) p μ := by
  rw [memLp_submodule_iff_coe, memLp_GradientSpace_iff]

end HeatKernel
