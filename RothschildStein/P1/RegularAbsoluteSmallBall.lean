-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ModelInputNearBounds
public import RothschildStein.P1.UniformModelSmallBallBound
public import RothschildStein.P1.TypeKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The actual regular component has a uniform
absolute small-ball integral bound on compact patches, retaining the chart density. -/
theorem exists_regular_uniform_absoluteSmallBall_bound
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ ρ A : ℝ, 0 < ρ ∧ 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      ‖∫ u in {u | ν u ≤ ε}, ‖r ξ ((C.e ξ).symm (-u)) * C.reflectedTransport ξ ψ u‖‖ ≤ A * ε := by
  obtain ⟨δ, L, hδ, hδ1, hL, _, hp⟩ := C.exists_inputModel_near_parameter_range hK hKU
  obtain ⟨B, hB, hb⟩ := C.exists_reflectedTransport_near_bound ψ hK hKU δ
  obtain ⟨M, hm⟩ := (hK.prod hL).exists_bound_of_continuousOn hr.1.continuous.continuousOn
  have he : 1 - (C.G.homogeneousDimension : ℝ) ≤ 0 := by
    have hQ : (1 : ℝ) ≤ C.G.homogeneousDimension := by
      exact_mod_cast G2.homogeneousDimension_pos C.G
    linarith
  apply uniformModel_smallBall_bound C.G hν
    (fun ξ u => ‖r ξ ((C.e ξ).symm (-u)) * C.reflectedTransport ξ ψ u‖)
    hδ (mul_nonneg (le_max_right M 0) hB)
  intro ξ hξ u hu hsmall
  have hR : ‖r ξ ((C.e ξ).symm (-u))‖ ≤ max M 0 :=
    (hm (ξ, (C.e ξ).symm (-u)) ⟨hξ, hp ξ hξ u hsmall⟩).trans (le_max_left _ _)
  have hpow : 1 ≤ kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (kgauge_pos C.G hu) (hsmall.trans hδ1) he
  rw [norm_norm, norm_mul]
  calc
    _ ≤ max M 0 * B := mul_le_mul hR (hb ξ hξ u hsmall) (norm_nonneg _) (le_max_right _ _)
    _ ≤ (max M 0 * B) * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) hB)

end RothschildStein.P1.LiftedChart
