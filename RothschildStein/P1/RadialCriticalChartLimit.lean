-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedChartTransport
public import RothschildStein.P1.RadialCriticalRegularization

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Smooth radial truncations of a
critical chart kernel converge to its scalar principal value with the full
reflected input density; the radial cutoff moment is proved zero. -/
theorem tendsto_radialCritical_inputChart
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν κ : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hκ : ContinuousOn κ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hh : ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      κ (C.G.dilate t u) = t ^ (-(C.G.homogeneousDimension : ℝ)) * κ u)
    (hc : H1.HasVanishingShellIntegrals ν κ)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hone : ∀ t : ℝ, t < r → Φ t = 1)
    (hout : ∀ t : ℝ, R ≤ t → Φ t = 0)
    (hb : ∀ u, ‖Φ (ν u)‖ ≤ 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η in C.U,
      (κ (C.Θ η ξ) * (1 - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))) * ψ η)
      (𝓝[>] (0 : ℝ))
      (𝓝 (H1.principalValueConvolution C.G ν κ
        (C.reflectedTransport ξ ψ ∘ C.G.inv) 0)) := by
  obtain ⟨hψ, hsψ⟩ := reflectedTransport_regular hξ ψ
  have ht := tendsto_radialCritical_scalar C.G hν hκ hh hc Φ hΦ hr hrR
    hone hout hb (C.reflectedTransport ξ ψ) hψ hsψ
  refine ht.congr' (Eventually.of_forall (fun ε => ?_))
  change (∫ u, (κ u * (1 - Φ (ν (C.G.dilate ε⁻¹ u)))) * C.reflectedTransport ξ ψ u) =
    ∫ η in C.U, (κ (C.Θ η ξ) * (1 - Φ (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))) * ψ η
  exact (integral_input_theta_mul hξ (fun u => κ u * (1 - Φ (ν (C.G.dilate ε⁻¹ u)))) ψ).symm

end RothschildStein.P1.LiftedChart
