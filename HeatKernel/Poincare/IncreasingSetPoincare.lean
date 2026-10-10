-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.IncreasingSetMeans
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace HeatKernel

/-- A uniform mean-oscillation seminorm bound on an increasing exhaustion passes to
its finite positive measure union, with the same bound. -/
theorem eLpNorm_mean_oscillation_le_of_increasing_sets
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {s : ℕ → Set A} {S : Set A}
    (hs : ∀ n, MeasurableSet (s n)) (hmono : Monotone s) (hunion : (⋃ n, s n) = S)
    (hfinite : μ S ≠ ⊤) (hpos : μ S ≠ 0) {f : A → ℝ} (hf : IntegrableOn f S μ)
    {p C : ℝ≥0∞}
    (hbound : ∀ n, eLpNorm (fun x => f x - ⨍ y in s n, f y ∂μ) p (μ.restrict (s n)) ≤ C) :
    eLpNorm (fun x => f x - ⨍ y in S, f y ∂μ) p (μ.restrict S) ≤ C := by
  have hS : MeasurableSet S := hunion ▸ MeasurableSet.iUnion hs
  have hsub : ∀ n, s n ⊆ S := fun n x hx => hunion ▸ mem_iUnion.mpr ⟨n, hx⟩
  let F := fun n => (s n).indicator (fun x => f x - ⨍ y in s n, f y ∂μ)
  have hF : ∀ n, AEStronglyMeasurable (F n) (μ.restrict S) := fun n =>
    (hf.aestronglyMeasurable.sub aestronglyMeasurable_const).indicator (hs n)
  have hB : ∀ n, eLpNorm (F n) p (μ.restrict S) ≤ C := by
    intro n
    dsimp only [F]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hs n), Measure.restrict_restrict_of_subset (hsub n)]
    exact hbound n
  have hm := tendsto_average_on_increasing_sets hs hmono hunion hfinite hpos hf
  apply Lp.eLpNorm_le_of_ae_tendsto (u := (atTop : Filter ℕ)) (f := F) (Eventually.of_forall hB) hF
    (hf.aestronglyMeasurable.sub aestronglyMeasurable_const)
  filter_upwards [ae_restrict_mem hS] with x hx
  obtain ⟨n₀, hn₀⟩ := mem_iUnion.mp (hunion.symm ▸ hx : x ∈ ⋃ n, s n)
  have hmem : ∀ᶠ n in atTop, x ∈ s n :=
    (eventually_ge_atTop n₀).mono (fun n hn => hmono hn hn₀)
  apply (tendsto_const_nhds.sub hm).congr'
  filter_upwards [hmem] with n hn
  simp only [F, indicator_of_mem hn]

end HeatKernel
