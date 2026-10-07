-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputFamilyTruncationDifference
public import RothschildStein.P1.IntegrableChartTruncationLimit

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

/-- A transported small-ball bound gives an actual
uniform error estimate for the prescribed sharp integral and its limit. -/
theorem integrableFamily_uniform_truncation_error
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hLU : L ⊆ C.U)
    (hi : ∀ ξ ∈ L, Integrable (fun η => Ψ ξ η (C.Θ η ξ) * ψ η))
    {r A : ℝ}
    (hb : ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖∫ u in {u | ν u ≤ ε}, Ψ ξ ((C.e ξ).symm (-u)) u *
        C.reflectedTransport ξ ψ u‖ ≤ A * ε) :
    ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖(∫ η in {η | ε < ν (C.Θ η ξ)}, Ψ ξ η (C.Θ η ξ) * ψ η) -
        limUnder (𝓝[>] (0 : ℝ)) (fun δ : ℝ =>
          ∫ η in {η | δ < ν (C.Θ η ξ)}, Ψ ξ η (C.Θ η ξ) * ψ η)‖ ≤ A * ε := by
  intro ξ hξ ε hε hεr
  have ht := C.tendsto_integrableChart_truncation (hLU hξ) hν (hi ξ hξ)
    (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero])
  rw [ht.limUnder_eq]
  rw [C.inputFamily_truncation_sub_integral (hLU hξ) ν hν.1 Ψ ψ (hi ξ hξ) ε,
    norm_neg]
  exact hb ξ hξ ε hε hεr

end RothschildStein.P1.LiftedChart
