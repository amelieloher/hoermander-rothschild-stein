-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBoundaryIntegralSplit
public import RothschildStein.P1.PrincipalInputRemainderFlux
public import RothschildStein.P1.EndpointFluxMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The actual input boundary flux of a critical
principal term converges to its constructed compact smooth multiplier.
Both endpoint cutoffs and the positive chart density are retained. -/
theorem tendsto_criticalPrincipal_input_boundary_flux
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (i : Fin k)
    (hd : t.degree = 2 - ((w i : ℕ) : ℤ))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) η) * t.kernel ξ η * φ η)
      (𝓝[>] (0 : ℝ))
      (𝓝 (C.endpointFluxMultiplier F (subset_closure.trans hF.closure_subset) t
        (hF.pole_smooth t.star) (fun v => C.Y i (-v)) (C.reflectedGenerator_contDiff i)
        θ hθ hsθ heθ ξ * φ ξ)) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨fun η => t.b η * φ η, t.b.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans (φ.tsupport_subset.trans hVU)⟩
  have htY := C.tendsto_criticalPrincipal_inputExteriorCutoff_flux hF t i hd hξ hθ hsθ heθ ψ
  have htR := C.tendsto_principal_input_remainder_flux hF t i hd.le hξ hθ hsθ heθ ψ
  have ht := (htY.add htR).const_mul (t.a ξ)
  simp only [add_zero] at ht
  have he (ε : ℝ) : (∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) η) * t.kernel ξ η * φ η) =
      t.a ξ * ((∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative (fun v => C.Y i (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
          C.reflectedTransport ξ ψ u) +
      ∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
          C.reflectedTransport ξ ψ u) := by
    rw [← C.integral_input_boundary_split hξ i t.modelKernel
      (t.modelKernel_contDiffOn (hF.pole_smooth t.star)).continuousOn hθ heθ ε ψ,
      ← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro η
    simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq, ψ, TestFunction.coe_mk]
    ring
  have hv : C.endpointFluxMultiplier F (subset_closure.trans hF.closure_subset) t
      (hF.pole_smooth t.star) (fun v => C.Y i (-v)) (C.reflectedGenerator_contDiff i)
      θ hθ hsθ heθ ξ * φ ξ =
      t.a ξ * ((C.c ξ * ψ ξ) * ∫ u, t.modelKernel ξ ξ u *
        fieldDerivative (fun v => C.Y i (-v)) (fun v => 1 - θ v) u) := by
    rw [C.endpointFluxMultiplier_apply]
    simp only [ψ, TestFunction.coe_mk]
    ring
  rw [hv]
  simpa only [he] using ht

end RothschildStein.P1.LiftedChart
