-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputRemainderFieldFlux
public import RothschildStein.P1.PrincipalInputCutoffFlux

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

/-- Every actual admissible principal term has
zero full reflected remainder flux, with its actual homogeneous degree. -/
theorem tendsto_principal_input_remainder_flux
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (i : Fin k)
    (hd : t.degree ≤ 2 - ((w i : ℕ) : ℤ))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hh := t.modelKernel_homogeneous (hF.pole_smooth t.star)
    (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star)
  rw [hF.G_eq] at hh
  have hdR : (t.degree : ℝ) ≤ 2 - ((w i : ℕ) : ℝ) := by exact_mod_cast hd
  apply C.tendsto_input_remainder_exterior_field_flux hξ i
    (β := 2 - C.G.homogeneousDimension - (t.degree : ℝ))
    (by linarith) t.modelKernel
    (t.modelKernel_contDiffOn (hF.pole_smooth t.star)).continuousOn hh hθ hsθ heθ ψ

end RothschildStein.P1.LiftedChart
