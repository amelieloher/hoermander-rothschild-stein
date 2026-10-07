-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesChain
public import RothschildStein.P1.PrincipalModelKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual principal cutoff kernel has
four derivative terms: the output cutoff, the endpoint parameter,
the homogeneous model field and the weighted chart remainder.
This is the pointwise identity off the diagonal in BB (11.18), p. 549;
the type estimates and the critical distributional limit are separate. -/
theorem LiftedChart.principal_fourTermLeibniz
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U)
    (hne : ξ ≠ η) (i : Fin k) :
    fieldDerivative (C.Xl i) (fun ζ => t.kernel ζ η) ξ =
      fieldDerivative (C.Xl i) t.a ξ * t.b η * t.modelKernel ξ η (C.Θ η ξ) +
      t.a ξ * t.b η *
        fderiv ℝ (kernelUncurry t.modelKernel) (ξ, η, C.Θ η ξ) (C.Xl i ξ, 0, 0) +
      t.a ξ * t.b η *
        fderiv ℝ (kernelUncurry t.modelKernel) (ξ, η, C.Θ η ξ)
          (0, 0, C.Y i (C.Θ η ξ)) +
      t.a ξ * t.b η *
        fderiv ℝ (kernelUncurry t.modelKernel) (ξ, η, C.Θ η ξ)
          (0, 0, C.R [i] η (C.Θ η ξ)) := by
  have hΨ : ContDiffOn ℝ 1 (kernelUncurry t.modelKernel) {z | z.2.2 ≠ 0} :=
    (t.modelKernel_contDiffOn hΓ).of_le (by simp)
  have hd := C.hasFDerivAt_kernel hΨ hη hξ hne
  have ha := (t.a.contDiff.differentiable (by simp) ξ).hasFDerivAt
  have hp := (ha.mul_const (t.b η)).mul hd
  simp only [Pi.mul_def] at hp
  have he : (fun ζ => t.kernel ζ η) =
      (fun ζ => t.a ζ * t.b η * t.modelKernel ζ η (C.Θ η ζ)) := by
    funext ζ
    simp only [PrincipalTerm.kernel, PrincipalTerm.modelKernel, hΘ]
  rw [he]
  change fderiv ℝ (fun ζ => t.a ζ * t.b η * t.modelKernel ζ η (C.Θ η ζ)) ξ
    (C.Xl i ξ) = _
  rw [hp.fderiv]
  have hc := C.fderiv_kernel_field hΨ hη hξ hne i
  have hs : (0, 0, C.Y i (C.Θ η ξ) + C.R [i] η (C.Θ η ξ)) =
      ((0, 0, C.Y i (C.Θ η ξ)) :
        (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) +
      (0, 0, C.R [i] η (C.Θ η ξ)) := by
    ext <;> simp
  rw [hs, map_add] at hc
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [← hd.fderiv, hc]
  simp only [fieldDerivative]
  ring

end RothschildStein.P1
