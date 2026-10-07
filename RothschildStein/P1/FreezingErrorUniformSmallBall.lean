-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformModelSmallBallBound
public import RothschildStein.P1.CriticalFamilyFreezingBound
public import RothschildStein.P1.JointModelTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}

/-- The actual endpoint-freezing error has a
uniform O(ε) small-ball integral against the full transported chart test.
The inverse chart and the chart density are retained in the estimate. -/
theorem exists_freezingError_uniform_smallBall_bound
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖∫ u in {u | ν u ≤ ε},
        ((D ξ ((C.e ξ).symm (-u))).apply Γ u - (D ξ ξ).apply Γ u) *
          C.reflectedTransport ξ ψ u‖ ≤ A * ε := by
  obtain ⟨δ, M, hδ, hM, hb⟩ := C.exists_criticalFamily_freezing_bound F Γ hΓ hhom hK hKU
  have hball : IsCompact {u : Fin (n + m) → ℝ | kgauge C.G u ≤ δ} :=
    G2.isCompact_gauge_sublevel C.G δ
  have hc : ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.reflectedTransport p.1 ψ p.2)
      (K ×ˢ {u | kgauge C.G u ≤ δ}) :=
    (C.reflectedTransport_joint_contDiffOn ψ).continuousOn.mono (fun p hp => ⟨hKU hp.1, mem_univ _⟩)
  obtain ⟨B, hB⟩ := (hK.prod hball).exists_bound_of_continuousOn hc
  apply uniformModel_smallBall_bound C.G hν
    (fun ξ u => ((D ξ ((C.e ξ).symm (-u))).apply Γ u - (D ξ ξ).apply Γ u) *
      C.reflectedTransport ξ ψ u) hδ (mul_nonneg hM (le_max_right B 0))
  intro ξ hξ u hu hsmall
  have hE : ‖(D ξ ((C.e ξ).symm (-u))).apply Γ u - (D ξ ξ).apply Γ u‖ ≤
      M * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ)) := by
    simpa only [← Real.rpow_intCast, Int.cast_sub, Int.cast_one, Int.cast_natCast]
      using hb ξ hξ u hu hsmall
  have hT : ‖C.reflectedTransport ξ ψ u‖ ≤ max B 0 :=
    (hB (ξ, u) ⟨hξ, hsmall⟩).trans (le_max_left B 0)
  rw [norm_mul]
  calc
    _ ≤ (M * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ))) * max B 0 :=
      mul_le_mul hE hT (norm_nonneg _)
        (mul_nonneg hM (Real.rpow_nonneg (kgauge_nonneg C.G u) _))
    _ = (M * max B 0) * kgauge C.G u ^ (1 - (C.G.homogeneousDimension : ℝ)) := by ring

end RothschildStein.P1.LiftedChart
