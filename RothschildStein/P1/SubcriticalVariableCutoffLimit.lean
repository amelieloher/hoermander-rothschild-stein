-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.VariableCriticalCutoffLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- Above the critical potential degree the moving
family has zero cutoff flux. The positive dilation power is retained,
so a subcritical term contributes no diagonal multiplier. -/
theorem tendsto_subcriticalVariableFieldCutoffTerm (G : HomogeneousGroup N)
    {Y : (Fin N → ℝ) → (Fin N → ℝ)} {w β : ℝ}
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y) (hhY : G2.IsHomogeneousField G Y w)
    (hβ : w - G.homogeneousDimension < β)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η, ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ β * Ψ ξ η u)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) × (Fin N → ℝ))
    (p₀ : (Fin N → ℝ) × (Fin N → ℝ))
    {θ : (Fin N → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hp : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ContinuousOn (fun u => p ε (G.dilate ε u)) (tsupport (fieldDerivative Y θ)) ∧
      ∀ u ∈ tsupport (fieldDerivative Y θ),
        (p ε (G.dilate ε u)).1 ∈ K ∧ (p ε (G.dilate ε u)).2 ∈ K)
    (htp : ∀ u ∈ tsupport (fieldDerivative Y θ),
      Tendsto (fun ε => p ε (G.dilate ε u)) (𝓝[>] (0 : ℝ)) (𝓝 p₀))
    (φ : (Fin N → ℝ) → ℝ) (hφ : Continuous φ) (hsφ : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ (p ε u).1 (p ε u).2 u *
      fieldDerivative Y (θ ∘ G.dilate ε⁻¹) u * φ u)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hD := H1.smooth_fieldDerivative Y hY θ hθ
  have hsD : HasCompactSupport (fieldDerivative Y θ) :=
    hsθ.of_isClosed_subset isClosed_closure (S.tsupport_fieldDerivative_subset Y θ)
  have h0D : (0 : Fin N → ℝ) ∉ tsupport (fieldDerivative Y θ) :=
    notMem_tsupport_iff_eventuallyEq.mpr (H1.fieldDerivative_cutoff_eventually_zero Y heθ)
  have ht := tendsto_compactParameter_poleIntegral G Ψ hΨ (fieldDerivative Y θ)
    hD.continuous hsD h0D (fun ε u => p ε (G.dilate ε u)) p₀ hK hp htp φ hφ hsφ
  have htε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : 0 < β + (G.homogeneousDimension : ℝ) - w := by linarith
  have hlim := (htε.rpow_const_nhds_zero hz).mul ht
  simp only [zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_variableFieldCutoff_dilate G hhY Ψ hhom (p ε) (φ := φ) hθ hε).symm

end RothschildStein.P1
