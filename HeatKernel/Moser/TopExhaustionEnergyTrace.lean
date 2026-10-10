-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionGoodEndpoints
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Nonlinear energy traces along good terminal times -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel

/-- Integrable fluxes converge under exhaustion by closed intervals whose terminal
times increase to the open top. -/
theorem tendsto_integral_Icc_of_cofinal_times {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b : ℝ) (s : ℕ → ℝ) (hm : Monotone s)
    (hs : ∀ n, s n ∈ Ioo a b) (ht : Tendsto s atTop (𝓝 b))
    (f : ℝ → V) (hf : IntegrableOn f (Ico a b) volume) :
    Tendsto (fun n => ∫ t in Icc a (s n), f t) atTop
      (𝓝 (∫ t in Ico a b, f t)) := by
  have he : (⋃ n, Icc a (s n)) = Ico a b := by
    ext t
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact ⟨hn.1, hn.2.trans_lt (hs n).2⟩
    · intro h
      obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_nhds h.2)).exists
      exact mem_iUnion.mpr ⟨n, h.1, hn.le⟩
  have hD : Monotone (fun n => Icc a (s n)) := by
    intro m n hmn t h
    exact ⟨h.1, h.2.trans (hm hmn)⟩
  have hi : IntegrableOn f (⋃ n, Icc a (s n)) volume := by rwa [he]
  simpa only [he] using tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hD hi

end HeatKernel
