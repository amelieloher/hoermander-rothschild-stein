-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.TopExhaustionGoodEndpoints
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Good initial times and integrals on bottom-sharing intervals -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel

/-- An almost everywhere property on an open interval holds along decreasing
interior times tending to its lower endpoint. -/
theorem exists_strictAnti_good_initial_times {a b : ℝ} (hab : a < b)
    {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume.restrict (Ioo a b), P t) :
    ∃ s : ℕ → ℝ, StrictAnti s ∧ (∀ n, a < s n ∧ s n < b ∧ P (s n)) ∧
      Tendsto s atTop (𝓝 a) := by
  have hd : Dense {t | t ∈ Ioo a b → P t} :=
    (volume : Measure ℝ).dense_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp hP)
  obtain ⟨s, hs, hm, ht⟩ := hd.exists_seq_strictAnti_tendsto_of_lt hab
  exact ⟨s, hs, fun n => ⟨(hm n).1.1, (hm n).1.2, (hm n).2 (hm n).1⟩, ht⟩

/-- Integrable fluxes converge on intervals whose initial times decrease to the
shared bottom. No value or trace at that bottom is required. -/
theorem tendsto_integral_Icc_of_decreasing_initial_times {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a b : ℝ) (s : ℕ → ℝ) (hm : Antitone s)
    (hs : ∀ n, s n ∈ Ioo a b) (ht : Tendsto s atTop (𝓝 a))
    (f : ℝ → V) (hf : IntegrableOn f (Ioc a b) volume) :
    Tendsto (fun n => ∫ t in Icc (s n) b, f t) atTop
      (𝓝 (∫ t in Ioc a b, f t)) := by
  have he : (⋃ n, Icc (s n) b) = Ioc a b := by
    ext t
    constructor
    · intro h
      obtain ⟨n, hn⟩ := mem_iUnion.mp h
      exact ⟨(hs n).1.trans_le hn.1, hn.2⟩
    · intro h
      obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_nhds h.1)).exists
      exact mem_iUnion.mpr ⟨n, hn.le, h.2⟩
  have hD : Monotone (fun n => Icc (s n) b) := by
    intro m n hmn t h
    exact ⟨(hm hmn).trans h.1, h.2⟩
  have hi : IntegrableOn f (⋃ n, Icc (s n) b) volume := by rwa [he]
  simpa only [he] using tendsto_setIntegral_of_monotone (fun _ => measurableSet_Icc) hD hi

end HeatKernel
