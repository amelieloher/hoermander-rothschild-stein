-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SmoothInputBoundaryIdentity
public import RothschildStein.P1.IntegrableChartRadialLimit
public import RothschildStein.P1.RadialGaugeCutoff
public import RothschildStein.P1.ContinuityPositive

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

/-- A locally C¹ input fiber has zero radial
boundary flux. Ordinary integration by parts and absolute-integral
convergence avoid any restriction comparing a field weight to Q. -/
theorem tendsto_smoothInput_boundary_flux
    (hF : C.IsLiftedFrame F) (i : Fin k)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {(0 : Fin (n + m) → ℝ)}ᶜ)
    (g : (Fin (n + m) → ℝ) → ℝ)
    (hg : ContDiffOn ℝ 1 g (F.V : Set (Fin (n + m) → ℝ)))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) * g η * φ η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hY : ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    (C.lift_smooth i).mono (hVU.trans C.U_subset_O)
  let dφ := S.wordDerivativeTest F.V C.Xl (fun j =>
    (C.lift_smooth j).mono (hVU.trans C.U_subset_O)) [i] φ
  have hcD : ContinuousOn (fieldDerivative (C.Xl i) g) (F.V : Set (Fin (n + m) → ℝ)) :=
    (hg.continuousOn_fderiv_of_isOpen F.V.isOpen (by rfl)).clm_apply hY.continuousOn
  let A := fun η => -fieldDerivative (C.Xl i) g η -
    g η * Hormander.Interface.euclideanDivergence (C.Xl i) η
  have hcA : ContinuousOn A (F.V : Set (Fin (n + m) → ℝ)) :=
    hcD.neg.sub (hg.continuousOn.mul
      (contDiffOn_euclideanDivergence F.V (C.Xl i) hY).continuousOn)
  have hiL := S.integrable_mul_test F.V
    (hg.continuousOn.locallyIntegrableOn (μ := volume) F.V.isOpen.measurableSet) dφ
  have hiR := S.integrable_mul_test F.V
    (hcA.locallyIntegrableOn (μ := volume) F.V.isOpen.measurableSet) φ
  have htL := C.tendsto_integrableChart_radialCutoff (hVU hξ) hν hiL
    (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (f := (dφ : (Fin (n + m) → ℝ) → ℝ))
        (fun ht => hη (hVU (dφ.tsupport_subset ht))), mul_zero])
    radialCutoffProfile radialCutoffProfile_contDiff.continuous (by norm_num : (0 : ℝ) < 2)
    (fun r hr => radialCutoffProfile_zero hr) (fun u => radialCutoffProfile_norm_le (ν u))
  have htR := C.tendsto_integrableChart_radialCutoff (hVU hξ) hν hiR
    (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (f := (φ : (Fin (n + m) → ℝ) → ℝ))
        (fun ht => hη (hVU (φ.tsupport_subset ht))), mul_zero])
    radialCutoffProfile radialCutoffProfile_contDiff.continuous (by norm_num : (0 : ℝ) < 2)
    (fun r hr => radialCutoffProfile_zero hr) (fun u => radialCutoffProfile_norm_le (ν u))
  have hibp := smoothInput_integral_integrationByParts F.V (C.Xl i) hY g hg φ
  have hv : (∫ η, g η * dφ η) - (∫ η, A η * φ η) = 0 := by
    change (∫ η, g η * fieldDerivative (C.Xl i) φ η) - (∫ η, A η * φ η) = 0
    rw [hibp]
    exact sub_self _
  have ht := htL.sub htR
  rw [hv] at ht
  refine ht.congr' (Eventually.of_forall (fun ε => ?_))
  have hΘ : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => C.Θ η ξ)
      (F.V : Set (Fin (n + m) → ℝ)) :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) (fun η hη => ⟨hVU hη, hVU hξ⟩)
  have hχ : ContDiffOn ℝ 1
      (fun η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (F.V : Set (Fin (n + m) → ℝ)) :=
    (contDiffOn_const.sub (((radialGaugeCutoff_contDiff hν hsν).comp
      (G2.contDiff_dilate C.G ε⁻¹)).comp_contDiffOn hΘ)).of_le (by simp)
  have he := smoothInput_boundary_integral_eq F.V (C.Xl i) hY g _ hg hχ φ
  simp only [dφ, S.wordDerivativeTest, TestFunction.coe_mk, wordDerivative, A] at he ⊢
  convert he.symm using 1
  congr 1 <;> apply integral_congr_ae <;>
    apply Eventually.of_forall <;> intro η <;> ring

end RothschildStein.P1.LiftedChart
