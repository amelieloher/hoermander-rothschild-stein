-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalFourTermLeibniz
public import RothschildStein.P1.PrincipalLeadingSum
public import RothschildStein.P1.PrincipalEndpointKernel
public import RothschildStein.P1.PrincipalCutoffDerivative
public import RothschildStein.P1.KernelFiberDerivatives

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual four-term derivative identity
with three contributions represented by the constructed principal kernels.
The fourth contribution is the actual weighted chart remainder derivative;
its typing and the weak endpoint limit are separate (BB (11.18), p. 549). -/
theorem LiftedChart.principal_fourTermConstructed
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (i : Fin k)
    (hhY : G2.IsHomogeneousField F.G (C.Y i) ((w i : ℕ) : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    fieldDerivative (C.Xl i) (fun ζ => t.kernel ζ η) ξ =
      (t.cutoffDerivative (C.Xl i) ((C.lift_smooth i).mono (hVU.trans C.U_subset_O))).kernel ξ η +
      t.endpointKernel (C.Xl i) ((C.lift_smooth i).mono (hVU.trans C.U_subset_O)) ξ η +
      t.leadingKernel (C.Y i) (C.model_field_smooth i) ((w i : ℕ) : ℤ) hhY ξ η +
      t.a ξ * t.b η * fieldDerivative (C.R [i] η) (t.modelKernel ξ η) (F.Θ η ξ) := by
  have hΨ : ContDiffOn ℝ 1 (kernelUncurry t.modelKernel) {z | z.2.2 ≠ 0} :=
    (t.modelKernel_contDiffOn hΓ).of_le (by simp)
  have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff hη hξ).not.mpr hne
  have h := C.principal_fourTermLeibniz F hΘ t hΓ hξ hη hne i
  rw [kernelUncurry_fderiv_parameter t.modelKernel hΨ ξ η (C.Θ η ξ) (C.Xl i ξ) 0 hu,
    kernelUncurry_fderiv_model t.modelKernel hΨ ξ η (C.Θ η ξ) (C.Y i (C.Θ η ξ)) hu,
    kernelUncurry_fderiv_model t.modelKernel hΨ ξ η (C.Θ η ξ) (C.R [i] η (C.Θ η ξ)) hu] at h
  have huF : F.Θ η ξ ≠ 0 := by rw [hΘ]; exact hu
  rw [PrincipalTerm.cutoffDerivative_kernel, PrincipalTerm.endpointKernel_eq,
    PrincipalTerm.leadingKernel_eq t (C.Y i) (C.model_field_smooth i) ((w i : ℕ) : ℤ) hhY hΓ ξ η huF]
  simpa only [hΘ, fieldDerivative] using h

end RothschildStein.P1
