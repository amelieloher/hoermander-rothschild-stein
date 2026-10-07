-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SharpInputChartIntegrability
public import RothschildStein.H1.PrincipalValueScalarPairing

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

/-- The actual sharp critical principal value in
input chart coordinates has integrable positive truncations and converges
to H1's scalar principal value with the full reflected test density. -/
theorem criticalInputChart_principalValue
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν κ : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hκ : ContinuousOn κ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hh : ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      κ (C.G.dilate t u) = t ^ (-(C.G.homogeneousDimension : ℝ)) * κ u)
    (hc : H1.HasVanishingShellIntegrals ν κ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∀ ε : ℝ, 0 < ε → IntegrableOn (fun η => κ (C.Θ η ξ) * ψ η)
      (C.U ∩ {η | ε < ν (C.Θ η ξ)}) volume) ∧
    Tendsto (fun ε : ℝ => ∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, κ (C.Θ η ξ) * ψ η)
      (𝓝[>] (0 : ℝ))
      (𝓝 (H1.principalValueConvolution C.G ν κ
        (C.reflectedTransport ξ ψ ∘ C.G.inv) 0)) := by
  refine ⟨fun ε hε => integrableOn_sharp_inputChart hξ hν hκ ψ hε, ?_⟩
  obtain ⟨hψ, hsψ⟩ := reflectedTransport_regular hξ ψ
  have ht := H1.tendsto_scalarPrincipalValue C.G hν hκ hh hc hψ hsψ
  refine ht.congr' (Eventually.of_forall (fun ε => ?_))
  change (∫ u in {u | ε < ν u}, κ u * C.reflectedTransport ξ ψ u) =
    ∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, κ (C.Θ η ξ) * ψ η
  exact (integral_sharp_inputChart hξ ν κ ψ hν.1 ε).symm

end RothschildStein.P1.LiftedChart
