-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology

namespace RothschildStein.G1

/-- Pull continuous coefficients back to the compact carrier subtype. -/
theorem continuousOn_compact_carrier_pullback {P E F : Type*}
    [TopologicalSpace P] [TopologicalSpace E] [TopologicalSpace F]
    {U : Set P} {K : Set E} {Z : P × E → F}
    (hZ : ContinuousOn Z (U ×ˢ K)) :
    ContinuousOn (fun q : P × K => Z (q.1, q.2.val)) (U ×ˢ univ) := by
  apply hZ.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
  intro q hq
  exact ⟨hq.1, q.2.property⟩

/-- A continuous family over a compact carrier converges uniformly
with its arbitrary locally compact parameter. -/
theorem uniformly_close_on_compact_carrier {P K F : Type*}
    [UniformSpace P] [LocallyCompactSpace P] [UniformSpace K] [CompactSpace K]
    [NormedAddCommGroup F] {U : Set P} (hU : IsOpen U)
    (Z : P × K → F) (hZ : ContinuousOn Z (U ×ˢ univ))
    {p₀ : P} (hp₀ : p₀ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, ∀ y : K, ‖Z (p, y) - Z (p₀, y)‖ < ε := by
  have hu : TendstoUniformly (fun p y => Z (p, y)) (fun y => Z (p₀, y)) (𝓝 p₀) :=
    ContinuousOn.tendstoUniformly (α := P) (β := K) (γ := F)
      (f := fun p y => Z (p, y)) (hU.mem_nhds hp₀) hZ
  have he := (Metric.tendstoUniformly_iff.mp hu) ε hε
  filter_upwards [he] with p hp
  intro y
  simpa only [dist_eq_norm, norm_sub_rev] using hp y

/-- Continuous coefficients converge uniformly on a compact
spatial carrier when their external parameter varies. No parameter
vector-space structure or parameter derivative is required (BB p. 452). -/
theorem fields_uniformly_close_on_compact {P E F : Type*}
    [UniformSpace P] [LocallyCompactSpace P] [UniformSpace E]
    [NormedAddCommGroup F] {U : Set P} (hU : IsOpen U) {K : Set E}
    (hK : IsCompact K) {Z : P × E → F} (hZ : ContinuousOn Z (U ×ˢ K))
    {p₀ : P} (hp₀ : p₀ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, ‖Z (p, y) - Z (p₀, y)‖ < ε := by
  let compactCarrierCompactSpace : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he := uniformly_close_on_compact_carrier hU (fun q : P × K => Z (q.1, q.2.val))
    (continuousOn_compact_carrier_pullback hZ) hp₀ hε
  filter_upwards [he] with p hp
  intro y hy
  exact hp ⟨y, hy⟩

end RothschildStein.G1
