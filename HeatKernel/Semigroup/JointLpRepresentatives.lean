-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.MeasurableLpApproximation

/-! # Jointly measurable representatives of measurable L² curves -/

@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology
namespace HeatKernel

theorem exists_jointly_measurable_L2_representative
    {α Y : Type*} [MeasurableSpace α] [MeasurableSpace Y] (μ : Measure Y)
    [MeasurableSpace (Lp ℝ 2 μ)] [BorelSpace (Lp ℝ 2 μ)] [SeparableSpace (Lp ℝ 2 μ)]
    (T : α → Lp ℝ 2 μ) (hT : Measurable T) :
    ∃ u : α × Y → ℝ, Measurable u ∧ ∀ a, (fun x => u (a, x)) =ᵐ[μ] T a := by
  obtain ⟨d, k, hk, hclose⟩ := exists_measurable_geometric_approximation T hT
  let v : ℕ → α → Lp ℝ 2 μ := fun n a => d (k n a)
  have hvm (n : ℕ) : Measurable (fun z : α × Y => v n z.1 z.2) := by
    have hd : Measurable (fun z : ℕ × Y => d z.1 z.2) :=
      measurable_from_prod_countable_right (fun j => (Lp.stronglyMeasurable (d j)).measurable)
    exact hd.comp (((hk n).comp measurable_fst).prodMk measurable_snd)
  let u : α × Y → ℝ := fun z => v 0 z.1 z.2 +
    ∑' n : ℕ, (v (n + 1) z.1 z.2 - v n z.1 z.2)
  refine ⟨u, (hvm 0).add (Measurable.tsum (fun n => (hvm (n + 1)).sub (hvm n))), ?_⟩
  intro a
  have hv : ∀ n, dist (T a) (v n a) < (1 / 2 : ℝ) ^ n := fun n => hclose n a
  have hs := hasSum_geometric_approximation_differences (fun n => v n a) (T a) hv
  have hnorm := summable_norm_geometric_approximation_differences (fun n => v n a) (T a) hv
  have hae := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  rw [hs.tsum_eq] at hae
  have hsub : ∀ᵐ x ∂μ, ∀ n : ℕ,
      (v (n + 1) a - v n a) x = v (n + 1) a x - v n a x :=
    ae_all_iff.mpr (fun n => Lp.coeFn_sub _ _)
  filter_upwards [hae, hsub, Lp.coeFn_sub (T a) (v 0 a)] with x hx hxn hx0
  have hsum : (∑' n : ℕ, (v (n + 1) a x - v n a x)) = T a x - v 0 a x := by
    simpa only [hxn, hx0, Pi.sub_apply] using hx.tsum_eq
  change v 0 a x + (∑' n : ℕ, (v (n + 1) a x - v n a x)) = T a x
  rw [hsum]
  ring

end HeatKernel
