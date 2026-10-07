-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformGaugeCriticalTruncationError
public import RothschildStein.P1.JointModelTransport
public import RothschildStein.P1.CriticalVariableFamilyChartLimit

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

/-- The family with parameter evaluated at a fixed point and the transported
chart test have a uniform prescribed-PV truncation error on compact
center sets. Shell cancellation and the compact support are discharged. -/
theorem exists_frozenFamily_uniform_truncation_error_bound
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖(∫ u in {u | ε < ν u}, (D ξ ξ).apply Γ u * C.reflectedTransport ξ ψ u) -
        H1.principalValueConvolution C.G ν ((D ξ ξ).apply Γ)
          (C.reflectedTransport ξ ψ ∘ C.G.inv) 0‖ ≤ A * ε := by
  obtain ⟨L, hL, hs⟩ := C.exists_uniform_modelTransport_support ψ hK hKU
  have hNeg : IsCompact ((fun u : Fin (n + m) → ℝ => -u) '' L) := hL.image continuous_neg
  have hz : ∀ ξ ∈ K, ∀ u, u ∉ (fun v : Fin (n + m) → ℝ => -v) '' L →
      C.reflectedTransport ξ ψ u = 0 := by
    intro ξ hξ u hu
    change C.modelTransport ξ ψ (-u) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    exact hu ⟨-u, hs ξ hξ ht, neg_neg u⟩
  have hh : ∀ ξ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      (D ξ η).apply Γ (C.G.dilate r u) =
        r ^ (-(C.G.homogeneousDimension : ℝ)) * (D ξ η).apply Γ u := by
    intro ξ η r hr u hu
    simpa only [Nat.cast_zero, zero_sub, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
      using F.apply_dilate hΓ hhom ξ η hr hu
  have hcancel (ξ : Fin (n + m) → ℝ) :
      H1.HasVanishingShellIntegrals ν ((D ξ ξ).apply Γ) :=
    H1.vanishingShellIntegrals_homogeneousDerivative C.G (D ξ ξ)
      (by norm_num : (0 : ℝ) < 2) (F.homogeneous ξ ξ) hν hΓ.continuousOn
      (fun α _ => hΓ.of_le (by simp)) hhom
  exact exists_uniformGaugeCritical_truncation_error_bound C.G hν
    (fun ξ η u => (D ξ η).apply Γ u) (F.contDiffOn_kernelUncurry hΓ).continuousOn
    hh hcancel C.isOpen_U (fun p => C.reflectedTransport p.1 ψ p.2)
    (C.reflectedTransport_joint_contDiffOn ψ) hK hKU hNeg hz

end RothschildStein.P1.LiftedChart
