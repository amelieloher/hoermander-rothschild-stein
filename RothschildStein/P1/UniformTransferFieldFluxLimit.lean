-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformTransferFieldFluxBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The complete transfer remainder flux
converges uniformly to zero on every compact output set in the chart,
including the critical degree (BB Theorem 11.24, p. 557). -/
theorem tendstoUniformlyOn_transfer_remainder_field_flux
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) (i : Fin k)
    {β : ℝ} (hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤ β)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate r u) = r ^ β * Ψ ζ η u)
    {θ : (Fin (n+m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    TendstoUniformlyOn (fun ε : ℝ => fun ξ => ∫ u,
      Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
        (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u)
      (fun _ => 0) (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨A, _, hb⟩ := C.exists_uniform_transfer_field_flux_bound hK hKU i hβ Ψ hΨ hhom hθ hsθ heθ ψ
  have ht : Tendsto (fun ε : ℝ => A * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul A
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  filter_upwards [hb, ht.eventually (Iio_mem_nhds hδ)] with ε hε hεδ
  intro ξ hξ
  rw [dist_zero_left]
  exact (hε ξ hξ).trans_lt hεδ

end RothschildStein.P1.LiftedChart
