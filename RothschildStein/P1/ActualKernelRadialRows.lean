-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.IntegrableRadialRowData
public import RothschildStein.P1.CriticalPrincipalRadialAgreement
public import RothschildStein.P1.StandardTypeSharpLimits
public import RothschildStein.P1.FiniteInputAdjointIdentity
public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.P1.PrincipalRowIntegrability
public import RothschildStein.P1.RegularKernelIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Each actual principal term has finite
integrability and a common sharp/radial value on a standard frame. -/
def principalInput_radialSharpRowData (hF : C.IsStandardFrame F H K hQ)
    (t : PrincipalTerm F) (hd : t.degree ≤ 2) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    RadialSharpRowData (fun η => H.norm (C.Θ η ξ))
      (fun ε η => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun η => t.kernel ξ η * φ η) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.lifted.closure_subset
  by_cases he : t.degree = 2
  · have hsharp := C.isTypeKernel_zero_sharpValue hF (t.isTypeKernel 0 (by simpa using hd)) φ ξ
    simp only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] at hsharp
    refine ⟨_, hsharp.1, ?_, hsharp.2, ?_⟩
    · intro ε _
      have hi := C.isTypeKernel_integrable_inputCutoff hF.lifted
        (t.isTypeKernel 0 (by simpa using hd)) hξ
        (radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth)
        (radialGaugeCutoff_eventually_one H.norm.gauge) ε φ
      exact hi.congr (Eventually.of_forall (fun η => by ring))
    · simpa only [mul_assoc] using
        C.tendsto_criticalPrincipal_radial_to_sharp hF.lifted t he (hVU hξ) H.norm.gauge φ
  · have hrow := C.integrable_principal_row F hF.lifted.G_eq hF.lifted.Θ_eq hVU t
      (by omega) (hF.lifted.pole_smooth t.star)
      (by simpa only [hF.lifted.G_eq] using hF.lifted.pole_homogeneous t.star) ξ
    have hM := Classical.choose_spec
      (φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous)
    have hi : Integrable (fun η => t.kernel ξ η * φ η) :=
      hrow.mul_bdd φ.contDiff.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    exact C.integrableRadialRowData (hVU hξ) H.norm.gauge hi
      (fun η hη => by
        rw [image_eq_zero_of_notMem_tsupport (f := (φ : (Fin (n + m) → ℝ) → ℝ))
          (fun ht => hη (hVU (φ.tsupport_subset ht))), mul_zero])

/-- A regular decomposition component has a
common sharp and smooth absolute-integral value on every interior test. -/
def regularInput_radialSharpRowData (hF : C.IsStandardFrame F H K hQ)
    {b : ℕ} {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsRegularKernel F b r) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    RadialSharpRowData (fun η => H.norm (C.Θ η ξ))
      (fun ε η => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun η => r ξ η * φ η) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.lifted.closure_subset
  have hM := Classical.choose_spec
    (φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous)
  have hi : Integrable (fun η => r ξ η * φ η) :=
    (hr.integrable_slices ξ).1.mul_bdd φ.contDiff.continuous.aestronglyMeasurable
      (Eventually.of_forall hM)
  exact C.integrableRadialRowData (hVU hξ) H.norm.gauge hi
    (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (f := (φ : (Fin (n + m) → ℝ) → ℝ))
        (fun ht => hη (hVU (φ.tsupport_subset ht))), mul_zero])

/-- The complete actual type-zero kernel has
common prescribed sharp and radial limits, by finite assembly of its
principal and regular components. -/
def typeZeroInput_radialSharpRowData (hF : C.IsStandardFrame F H K hQ)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F 0 κ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    RadialSharpRowData (fun η => H.norm (C.Θ η ξ))
      (fun ε η => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun η => κ ξ η * φ η) := by
  let rsActualRadialRowFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let d : TypeDecomposition F 0 1 κ := Classical.choice (hκ 1)
  let DP := RadialSharpRowData.listSum d.principal (fun t η => t.kernel ξ η * φ η)
    (fun t ht => C.principalInput_radialSharpRowData hF t
      (by simpa using d.principal_degree t ht) φ hξ)
  let DR := C.regularInput_radialSharpRowData hF d.regular_isRegular φ hξ
  apply (DP.add DR).congr_ae
  filter_upwards [volume.ae_ne ξ] with η hηξ
  change (d.principal.map (fun t => t.kernel ξ η * φ η)).sum + d.regular ξ η * φ η = κ ξ η * φ η
  rw [d.eq_off_diagonal ξ η hηξ.symm, List.sum_map_mul_right]
  ring

end RothschildStein.P1.LiftedChart
