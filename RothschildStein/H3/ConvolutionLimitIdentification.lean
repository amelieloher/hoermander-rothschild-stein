-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactUniformConvolutionLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.H3

/-- The limit chosen from actual convolution approximants
agrees on its domain with the actual convolution of the limiting
compact source. The common compact integration region is supplied by
the shared dominated convergence theorem (BB pp. 386–387). -/
theorem groupConvolution_eqOn_of_uniform_source_and_pointwise_limits {N : ℕ}
    (G : HomogeneousGroup N) (K f : (Fin N → ℝ) → ℝ)
    (hK : LocallyIntegrable K volume) (hf : Continuous f)
    (S : Set (Fin N → ℝ)) (hS : IsCompact S) (hsf : Function.support f ⊆ S)
    (φ F : ℕ → (Fin N → ℝ) → ℝ) (v : (Fin N → ℝ) → ℝ)
    (hφ : ∀ n, Continuous (φ n) ∧ Function.support (φ n) ⊆ S)
    (hsource : TendstoUniformly φ f atTop)
    (hF : ∀ n, F n = G2.groupConvolution G (φ n) K)
    (U : Set (Fin N → ℝ))
    (hlim : ∀ x ∈ U, Tendsto (fun n => F n x) atTop (𝓝 (v x))) :
    EqOn v (G2.groupConvolution G f K) U := by
  intro x hx
  have hc := tendsto_groupConvolution_of_uniform_compact_support G atTop φ f K
    hK hf S hS hsf (Eventually.of_forall hφ) hsource x
  have hv := (hlim x hx).congr (fun n => congrFun (hF n) x)
  exact tendsto_nhds_unique hv hc

end RothschildStein.H3
