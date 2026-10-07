-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SubcriticalVariableCutoffLimit
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

/-- An actual subcritical principal term has
zero moving-endpoint generator flux. Only the critical degree can
contribute a diagonal multiplier. -/
theorem tendsto_subcriticalPrincipal_inputCutoff_flux
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (i : Fin k)
    (hd : t.degree < 2 - ((w i : ℕ) : ℤ))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hsθ : HasCompactSupport θ) (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ u, t.modelKernel ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.Y i (-v)) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let Y := fun v => C.Y i (-v)
  have hsD : HasCompactSupport (fieldDerivative Y θ) :=
    hsθ.of_isClosed_subset isClosed_closure (S.tsupport_fieldDerivative_subset Y θ)
  obtain ⟨L, hL, hp, htp⟩ := C.exists_rescaledInput_parameter_range
    (isCompact_singleton (x := ξ)) (singleton_subset_iff.mpr hξ) hsD.isCompact
  obtain ⟨hcψ, hsψ⟩ := C.reflectedTransport_regular hξ ψ
  have hh := t.modelKernel_homogeneous (hF.pole_smooth t.star)
    (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star)
  rw [hF.G_eq] at hh
  have hdR : (t.degree : ℝ) < 2 - ((w i : ℕ) : ℝ) := by exact_mod_cast hd
  exact tendsto_subcriticalVariableFieldCutoffTerm C.G
    (C.reflectedGenerator_contDiff i) (C.reflectedGenerator_homogeneous i)
    (by linarith) t.modelKernel
    (t.modelKernel_contDiffOn (hF.pole_smooth t.star)).continuousOn hh
    (fun _ u => (ξ, (C.e ξ).symm (-u))) (ξ, ξ) hθ hsθ heθ hL
    (hp.mono (fun _ h => h ξ (mem_singleton ξ)))
    (fun u _ => htp ξ (mem_singleton ξ) u) (C.reflectedTransport ξ ψ) hcψ.continuous hsψ

end RothschildStein.P1.LiftedChart
