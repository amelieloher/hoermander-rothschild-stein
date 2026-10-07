-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.AmbientTruncationLocalization
public import RothschildStein.P1.CriticalInputChartPrincipalValue

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

/-- The critical chart principal value uses the
actual ambient truncation sets. Compact test support supplies localization;
no global regularity of Θ outside its chart is assumed. -/
theorem criticalInputChart_principalValue_ambient
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν κ : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hκ : ContinuousOn κ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hh : ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      κ (C.G.dilate t u) = t ^ (-(C.G.homogeneousDimension : ℝ)) * κ u)
    (hc : H1.HasVanishingShellIntegrals ν κ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∀ ε : ℝ, 0 < ε → IntegrableOn (fun η => κ (C.Θ η ξ) * ψ η)
      {η | ε < ν (C.Θ η ξ)} volume) ∧
    Tendsto (fun ε : ℝ => ∫ η in {η | ε < ν (C.Θ η ξ)}, κ (C.Θ η ξ) * ψ η)
      (𝓝[>] (0 : ℝ))
      (𝓝 (H1.principalValueConvolution C.G ν κ
        (C.reflectedTransport ξ ψ ∘ C.G.inv) 0)) := by
  have hz : ∀ η, η ∉ C.U → κ (C.Θ η ξ) * ψ η = 0 := by
    intro η hη
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  obtain ⟨hi, ht⟩ := criticalInputChart_principalValue hξ hν hκ hh hc ψ
  refine ⟨fun ε hε => ?_, ?_⟩
  · apply (integrableOn_localizedTruncation_iff C.isOpen_U.measurableSet hz).mp
    simpa only [inter_comm] using hi ε hε
  · refine ht.congr' (Eventually.of_forall (fun ε => ?_))
    change (∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, κ (C.Θ η ξ) * ψ η) =
      ∫ η in {η | ε < ν (C.Θ η ξ)}, κ (C.Θ η ξ) * ψ η
    simpa only [inter_comm] using
      (integral_localizedTruncation (A := {η | ε < ν (C.Θ η ξ)}) C.isOpen_U.measurableSet hz)

end RothschildStein.P1.LiftedChart
