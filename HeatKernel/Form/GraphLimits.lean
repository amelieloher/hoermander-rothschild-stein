-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SmoothGradientCore
public import HeatKernel.Form.SmoothGraphLimits

/-!
# Componentwise limits in the energy graph

Convergence of the function and of each horizontal derivative in L² is convergence in the
graph norm. The closed energy graph therefore contains every such limit.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace HeatKernel

/-- Componentwise L² convergence implies convergence of function-gradient pairs. -/
theorem tendsto_GradientSpace_iff {N q : ℕ} (U : Opens (Fin N → ℝ))
    {α : Type*} {l : Filter α} {v : α → GradientSpace U q} {w : GradientSpace U q} :
    Tendsto v l (𝓝 w) ↔
      Tendsto (fun a => (v a).fst) l (𝓝 w.fst) ∧
      ∀ i, Tendsto (fun a => (v a).snd i) l (𝓝 (w.snd i)) := by
  constructor
  · intro h
    exact ⟨(by fun_prop : Continuous (fun z : GradientSpace U q => z.fst)).continuousAt.tendsto.comp h,
      fun i => (by fun_prop : Continuous (fun z : GradientSpace U q => z.snd i)).continuousAt.tendsto.comp h⟩
  · rintro ⟨hf, hg⟩
    have hp := ((PiLp.continuous_toLp 2
      (fun _ : Fin q => SpatialL2 U)).tendsto _).comp (tendsto_pi_nhds.mpr hg)
    exact (((WithLp.homeomorphProd 2 (SpatialL2 U)
      (PiLp 2 (fun _ : Fin q => SpatialL2 U))).symm.continuous).tendsto _).comp
        (hf.prodMk_nhds hp)

/-- The energy graph is stable under componentwise L² limits. -/
theorem mem_energyGraph_of_componentwise_tendsto {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    {v : ℕ → GradientSpace U q} {w : GradientSpace U q}
    (hv : ∀ n, v n ∈ energyGraph U X)
    (hf : Tendsto (fun n => (v n).fst) atTop (𝓝 w.fst))
    (hg : ∀ i, Tendsto (fun n => (v n).snd i) atTop (𝓝 (w.snd i))) :
    w ∈ energyGraph U X :=
  (isClosed_energyGraph U X).mem_of_tendsto
    ((tendsto_GradientSpace_iff U).mpr ⟨hf, hg⟩) (Eventually.of_forall hv)

end HeatKernel
