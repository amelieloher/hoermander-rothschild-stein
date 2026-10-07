-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberParameterization
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.L1

/-- The actual derivative chain for the fiber chart has
identity horizontal output and the actual vertical derivative. This follows
from the local horizontal identity, not from a matrix-chain premise. -/
theorem fiber_parameterization_derivative_chain {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : Set (E × F)} (hU : IsOpen U) (hV : IsOpen V)
    (Φ : E × F → E × F) (θ : E × F → E)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ U) (hθ : ContDiffOn ℝ (⊤ : ℕ∞) θ V)
    (hmap : ∀ p ∈ V, (θ p, p.2) ∈ U)
    (hbase : ∀ p ∈ V, (Φ (θ p, p.2)).1 = p.1) {p : E × F} (hp : p ∈ V) :
    (fderiv ℝ Φ (θ p, p.2)).comp
        ((fderiv ℝ θ p).prod (ContinuousLinearMap.snd ℝ E F)) =
      (ContinuousLinearMap.fst ℝ E F).prod
        (fderiv ℝ (fun q : E × F => (Φ (θ q, q.2)).2) p) := by
  have hθd := (hθ.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hΦd := (hΦ.contDiffAt (hU.mem_nhds (hmap p hp))).differentiableAt (by simp)
  have hc : HasFDerivAt (fun q : E × F => Φ (θ q, q.2))
      ((fderiv ℝ Φ (θ p, p.2)).comp
        ((fderiv ℝ θ p).prod (ContinuousLinearMap.snd ℝ E F))) p :=
    hΦd.hasFDerivAt.comp p (hθd.hasFDerivAt.prodMk hasFDerivAt_snd)
  have hσd := ((contDiffOn_fiber_parameterization Φ θ hΦ hθ hmap).contDiffAt
    (hV.mem_nhds hp)).differentiableAt (by simp)
  have ho : HasFDerivAt (fun q : E × F => (q.1, (Φ (θ q, q.2)).2))
      ((ContinuousLinearMap.fst ℝ E F).prod
        (fderiv ℝ (fun q : E × F => (Φ (θ q, q.2)).2) p)) p :=
    hasFDerivAt_fst.prodMk hσd.hasFDerivAt
  have he : (fun q : E × F => Φ (θ q, q.2)) =ᶠ[𝓝 p]
      (fun q : E × F => (q.1, (Φ (θ q, q.2)).2)) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact Prod.ext (hbase q hq) rfl
  have hh := he.fderiv_eq (𝕜 := ℝ)
  rw [hc.fderiv, ho.fderiv] at hh
  exact hh

end RothschildStein.L1
