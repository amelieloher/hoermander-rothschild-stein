-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalCutoffWeakTransfer
public import RothschildStein.P1.PhysicalTransferFluxIntegrability
public import RothschildStein.P1.TransferFluxTransport
public import RothschildStein.P1.PositiveTypeRowIntegrability
public import RothschildStein.P1.IntegrableModelMultiplier
public import RothschildStein.P1.PrincipalCutoffKernel

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
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The finite principal error row splits
into its typed error truncation and its full reflected remainder flux.
Both summands are integrable before the integral is split (BB p. 557). -/
theorem principalRadial_errorRow_eq (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) (i : Fin k) {mu : ℕ} (hmu : 1 ≤ mu)
    (hE : IsTypeKernel F mu (C.principalTransferErrorKernel F hF t i))
    {θ : (Fin (n+m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 1)
    (hbθ : ∀ u, ‖θ u‖ ≤ 1) (ε : ℝ)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n+m) → ℝ))) :
    (∫ η, C.regularTransferErrorKernel F i
      (fun x y => (1 - θ (C.G.dilate ε⁻¹ (F.Θ y x))) * t.kernel x y) ξ η * φ η) =
      (∫ η, (1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) *
        (C.principalTransferErrorKernel F hF t i ξ η * φ η)) +
      ∫ u, t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
          ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ φ u := by
  let rsPrincipalRadialFinNonempty : Nonempty (Fin (n+m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
  let χ := (fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := (contDiff_const.sub hθ).comp (G2.contDiff_dilate C.G ε⁻¹)
  have hbχ (u : Fin (n+m) → ℝ) : ‖χ u‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℝ) (θ (C.G.dilate ε⁻¹ u))
    have hh := hbθ (C.G.dilate ε⁻¹ u)
    change ‖1 - θ (C.G.dilate ε⁻¹ u)‖ ≤ 2
    norm_num only [norm_one] at hn
    linarith
  have hrow := (C.positiveType_rowIntegrable F hF.G_eq hF.Θ_eq hVU hF.pole_smooth
    (fun star => by simpa only [hF.G_eq] using hF.pole_homogeneous star)
    mu hmu _ hE ξ).1
  obtain ⟨B, hB⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  have hiE := hrow.mul_bdd φ.contDiff.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hiχE := C.integrable_modelMultiplier (hVU hξ) hiE
    (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (fun hs => hη (hVU (φ.tsupport_subset hs))), mul_zero])
    χ hχ.continuous hbχ
  have hiFlux := C.integrable_physicalTransfer_exteriorFlux (hVU hξ) i t.cutoffModelKernel
    (t.cutoffModelKernel_contDiffOn (hF.pole_smooth t.star)).continuousOn hθ heθ ε ψ
  have he : (fun η => C.regularTransferErrorKernel F i
      (fun x y => (1 - θ (C.G.dilate ε⁻¹ (F.Θ y x))) * t.kernel x y) ξ η * φ η) =ᵐ[volume]
      (fun η => χ (C.Θ η ξ) * (C.principalTransferErrorKernel F hF t i ξ η * φ η) +
        t.cutoffModelKernel ξ η (C.Θ η ξ) *
          fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) * ψ η) := by
    filter_upwards [volume.ae_ne ξ] with η hηξ
    by_cases hη : η ∈ (F.V : Set (Fin (n+m) → ℝ))
    · have hk := C.principalCutoff_transfer_error_eq F hF t i χ hχ (hVU hξ) (hVU hη) hηξ.symm
      change C.regularTransferErrorKernel F i (fun x y => χ (F.Θ y x) * t.kernel x y) ξ η * φ η = _
      rw [hk, PrincipalTerm.kernel_eq_cutoffModelKernel, hF.Θ_eq]
      change _ = χ (C.Θ η ξ) * (C.principalTransferErrorKernel F hF t i ξ η * φ η) +
        t.cutoffModelKernel ξ η (C.Θ η ξ) * fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) * φ η
      ring
    · have hz : φ η = 0 := by simpa using φ.zero_on_compl hη
      simp only [ψ, TestFunction.coe_mk, hz, mul_zero, add_zero]
  rw [integral_congr_ae he, integral_add hiχE hiFlux,
    C.integral_inputModel_transfer_flux (hVU hξ) i t.cutoffModelKernel χ ψ]
  rfl

end RothschildStein.P1.LiftedChart
