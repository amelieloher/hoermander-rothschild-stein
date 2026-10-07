-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Absolutely convergent integrals survive removal of
shrinking open truncations. BB pp. 304, 307–308; dominated convergence. -/
theorem tendsto_truncated_of_integrable {D : LocDoubling X} (d : TruncDist D)
    {G : Set X} (hG : MeasurableSet G) (hGΩ : G ⊆ D.Ω₁) {x : X} (hx : x ∈ D.Ω₁)
    {g : X → ℝ} (hg : IntegrableOn g G D.μ) :
    Tendsto (fun ε : ℝ => ∫ y in G ∩ {y | ε < d.d' x y}, g y ∂D.μ)
      (𝓝[>] 0) (𝓝 (∫ y in G, g y ∂D.μ)) := by
  classical
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  let F : ℝ → X → ℝ := fun ε => {y | ε < d.d' x y}.indicator g
  have hmeas : ∀ ε, AEStronglyMeasurable (F ε) (D.μ.restrict G) := fun ε =>
    hg.aestronglyMeasurable.indicator (measurableSet_lt measurable_const hm)
  have hb : ∀ ε, ∀ᵐ y ∂D.μ.restrict G, ‖F ε y‖ ≤ ‖g y‖ := fun ε => ae_of_all _ fun y => by
    dsimp [F]
    by_cases hy : ε < d.d' x y <;> simp [hy]
  have hae : ∀ᵐ y ∂D.μ, x ≠ y := by
    apply ae_iff.mpr
    simpa only [not_ne_iff, ofPred_eq_eq_singleton'] using D.noAtoms x
  have ht : ∀ᵐ y ∂D.μ.restrict G, Tendsto (fun ε => F ε y) (𝓝[>] 0) (𝓝 (g y)) := by
    filter_upwards [ae_restrict_mem hG, ae_restrict_of_ae hae] with y hy hxy
    have hd : 0 < d.d' x y := lt_of_lt_of_le
      (mul_pos d.θ₁_pos (dist_pos.mpr hxy)) (d.comp x hx y (hGΩ hy)).1
    have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, F ε y = g y :=
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds |>.mono fun ε hε => by
        exact Set.indicator_of_mem (s := {z | ε < d.d' x z}) (a := y) hε g
    exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)
  have he := tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖)
    (Eventually.of_forall hmeas) (Eventually.of_forall hb) hg.norm ht
  simpa only [F, integral_indicator (measurableSet_lt measurable_const hm),
    Measure.restrict_restrict (measurableSet_lt measurable_const hm), inter_comm] using he

end RothschildStein.H2
