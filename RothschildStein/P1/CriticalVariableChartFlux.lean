-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.VariableCriticalCutoffLimit
public import RothschildStein.P1.RescaledChartParameters
public import RothschildStein.P1.ReflectedChartTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The critical input-chart flux for the actual
variable family freezes to its diagonal value, including the reflected
Jacobian density. Compactness and convergence of the actual inverse
chart parameters are proved, rather than supplied as premises. -/
theorem tendsto_criticalVariable_inputChart_flux
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)} {a : ℝ}
    (hY : ContDiff ℝ (⊤ : ℕ∞) Y) (hhY : G2.IsHomogeneousField C.G Y a)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ζ η, ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      Ψ ζ η (C.G.dilate t u) = t ^ (a - C.G.homogeneousDimension) * Ψ ζ η u)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative Y (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((C.c ξ * ψ ξ) * ∫ u, Ψ ξ ξ u * fieldDerivative Y θ u)) := by
  have hsD : HasCompactSupport (fieldDerivative Y θ) :=
    hsθ.of_isClosed_subset isClosed_closure (S.tsupport_fieldDerivative_subset Y θ)
  obtain ⟨L, hL, hp, htp⟩ := C.exists_rescaledInput_parameter_range
    (isCompact_singleton (x := ξ)) (singleton_subset_iff.mpr hξ) hsD.isCompact
  have hp' : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ContinuousOn (fun u => (ξ, (C.e ξ).symm (-C.G.dilate ε u)))
        (tsupport (fieldDerivative Y θ)) ∧
      ∀ u ∈ tsupport (fieldDerivative Y θ), ξ ∈ L ∧ (C.e ξ).symm (-C.G.dilate ε u) ∈ L :=
    hp.mono (fun _ h => h ξ (mem_singleton ξ))
  obtain ⟨hcψ, hsψ⟩ := C.reflectedTransport_regular hξ ψ
  have ht := tendsto_criticalVariableFieldCutoffTerm C.G hY hhY Ψ hΨ hhom
    (fun _ u => (ξ, (C.e ξ).symm (-u))) (ξ, ξ) hθ hsθ heθ hL hp'
    (fun u _ => htp ξ (mem_singleton ξ) u) (C.reflectedTransport ξ ψ) hcψ.continuous hsψ
  simpa only [C.reflectedTransport_zero hξ] using ht

end RothschildStein.P1.LiftedChart
