-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalVariableChartFlux
public import RothschildStein.P1.ReflectedModelGenerator
public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.P1.ContinuityPositive
public import RothschildStein.H1.FieldSubtractConstant

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
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The actual critical principal family has the
diagonal reflected-generator flux. The endpoint and Jacobian are not fixed
before taking the limit. -/
theorem tendsto_criticalPrincipal_inputCutoff_flux
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (i : Fin k)
    (hd : t.degree = 2 - ((w i : ℕ) : ℤ))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.Y i (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((C.c ξ * ψ ξ) * ∫ u, t.modelKernel ξ ξ u *
        fieldDerivative (fun v => C.Y i (-v)) θ u)) := by
  apply C.tendsto_criticalVariable_inputChart_flux hξ
    (C.reflectedGenerator_contDiff i) (C.reflectedGenerator_homogeneous i)
    t.modelKernel (t.modelKernel_contDiffOn (hF.pole_smooth t.star)).continuousOn
    ?_ hθ hsθ heθ ψ
  intro ζ η r hr u hu
  have hh := t.modelKernel_homogeneous (hF.pole_smooth t.star)
    (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star) ζ η r hr u hu
  rw [hF.G_eq, hd] at hh
  have he : (2 : ℝ) - C.G.homogeneousDimension -
      ((2 - ((w i : ℕ) : ℤ) : ℤ) : ℝ) = ((w i : ℕ) : ℝ) - C.G.homogeneousDimension := by
    push_cast
    ring
  simpa only [he] using hh

/-- The exterior principal cutoff has the opposite
flux sign. This is the cutoff used when integrating away from the pole. -/
theorem tendsto_criticalPrincipal_inputExteriorCutoff_flux
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (i : Fin k)
    (hd : t.degree = 2 - ((w i : ℕ) : ℤ))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.Y i (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((C.c ξ * ψ ξ) * ∫ u, t.modelKernel ξ ξ u *
        fieldDerivative (fun v => C.Y i (-v)) (fun v => 1 - θ v) u)) := by
  let Y := fun v => C.Y i (-v)
  have hder (ε : ℝ) : fieldDerivative Y ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) =
      fun u => -fieldDerivative Y (θ ∘ C.G.dilate ε⁻¹) u :=
    H1.fieldDerivative_one_sub_C1 Y
      ((hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).of_le (by simp))
  have hder₁ := H1.fieldDerivative_one_sub_C1 Y (hθ.of_le (by simp))
  have he (ε : ℝ) : (∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative Y ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) =
      -(∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative Y (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u) := by
    rw [hder, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall (fun u => by ring))
  have hc : ((C.c ξ * ψ ξ) * ∫ u, t.modelKernel ξ ξ u *
      fieldDerivative Y (fun v => 1 - θ v) u) =
      -((C.c ξ * ψ ξ) * ∫ u, t.modelKernel ξ ξ u * fieldDerivative Y θ u) := by
    rw [hder₁]
    have hh : (fun u => t.modelKernel ξ ξ u * -fieldDerivative Y θ u) =
        fun u => -(t.modelKernel ξ ξ u * fieldDerivative Y θ u) := by
      funext u
      ring
    rw [hh, integral_neg]
    ring
  change Tendsto (fun ε => ∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
    fieldDerivative Y ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u) _ (𝓝 _)
  rw [hc]
  simp_rw [he]
  exact (C.tendsto_criticalPrincipal_inputCutoff_flux hF t i hd hξ hθ hsθ heθ ψ).neg

end RothschildStein.P1.LiftedChart
