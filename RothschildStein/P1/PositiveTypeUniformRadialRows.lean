-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformRadialRows
public import RothschildStein.P1.PositivePrincipalUniformRadialError
public import RothschildStein.P1.RegularUniformRadialError
public import RothschildStein.P1.RegularTransferWeakIdentity

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
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n+m)}

/-- Actual radial row limits acquire their
finite cutoff integrability from bounded model multipliers. -/
theorem uniformRadialRows_of_rowLimit
    {ν : (Fin (n+m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U)
    {L : Set (Fin (n+m) → ℝ)} (hLU : L ⊆ C.U)
    (hi : ∀ ξ ∈ L, Integrable (fun η => κ ξ η * φ η))
    (ht : TendstoUniformlyOn (fun ε : ℝ => fun ξ => ∫ η,
      (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * (κ ξ η * φ η))
      (fun ξ => ∫ η, κ ξ η * φ η) (𝓝[>] (0 : ℝ)) L) :
    UniformRadialRows L
      (fun ε ξ η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun ξ η => κ ξ η * φ η) where
  integrable := hi
  cutoff_integrable := by
    intro ξ hξ ε
    apply C.integrable_modelMultiplier (B := 2) (hLU hξ) (hi ξ hξ)
      (fun η hη => by
        rw [image_eq_zero_of_notMem_tsupport (fun hs => hη (hVU (φ.tsupport_subset hs))), mul_zero])
      (fun u => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ u)))
      (continuous_const.sub (radialCutoffProfile_contDiff.continuous.comp
        (hν.1.comp (G2.continuous_dilate C.G ε⁻¹))))
    intro u
    have hb := norm_sub_le (1 : ℝ) (radialCutoffProfile (ν (C.G.dilate ε⁻¹ u)))
    have hh := radialCutoffProfile_norm_le (ν (C.G.dilate ε⁻¹ u))
    norm_num only [norm_one] at hb
    linarith
  limit := ht

/-- Positive principal components provide
actual finite radial integrability and compact-uniform convergence. -/
theorem principalInput_uniformRadialRows (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) (hd : t.degree ≤ 1)
    {ν : (Fin (n+m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n+m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    UniformRadialRows L
      (fun ε ξ η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun ξ η => t.kernel ξ η * φ η) := by
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  apply C.uniformRadialRows_of_rowLimit hν t.kernel φ hVU hLU
  · intro ξ _
    have hrow := C.integrable_principal_row F hF.G_eq hF.Θ_eq hVU t hd
      (hF.pole_smooth t.star) (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star) ξ
    obtain ⟨B, hB⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
    exact hrow.mul_bdd φ.contDiff.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  · exact C.tendstoUniformlyOn_positivePrincipal_radialIntegral hF t hd hν φ hL hLU

/-- Regular components provide actual finite
radial integrability and compact-uniform convergence. -/
theorem regularInput_uniformRadialRows (hF : C.IsLiftedFrame F)
    {r : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ} (hr : IsRegularKernel F 1 r)
    {ν : (Fin (n+m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n+m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    UniformRadialRows L
      (fun ε ξ η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun ξ η => r ξ η * φ η) :=
  C.uniformRadialRows_of_rowLimit hν r φ (subset_closure.trans hF.closure_subset) hLU
    (fun ξ _ => hr.transfer_row_integrable ξ φ)
    (C.tendstoUniformlyOn_regular_radialIntegral hF hr hν φ hL hLU)

/-- Every actual positive-type kernel has
compact-uniform whole radial convergence. One finite decomposition
suffices, and arbitrary diagonal values are removed only almost everywhere. -/
theorem positiveTypeInput_uniformRadialRows {lam : ℕ} (hlam : 1 ≤ lam)
    (hF : C.IsLiftedFrame F)
    {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ} (hκ : IsTypeKernel F lam κ)
    {ν : (Fin (n+m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n+m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    UniformRadialRows L
      (fun ε ξ η => 1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))
      (fun ξ η => κ ξ η * φ η) := by
  let rsPositiveRadialFinNonempty : Nonempty (Fin (n+m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let d : TypeDecomposition F lam 1 κ := Classical.choice (hκ 1)
  let DP := UniformRadialRows.listSum d.principal (fun t ξ η => t.kernel ξ η * φ η)
    (fun t ht => C.principalInput_uniformRadialRows hF t
      (by have hd := d.principal_degree t ht; omega) hν φ hL hLU)
  let DR := C.regularInput_uniformRadialRows hF d.regular_isRegular hν φ hL hLU
  apply (DP.add DR).congr_ae
  intro ξ _
  filter_upwards [volume.ae_ne ξ] with η hηξ
  change (d.principal.map (fun t => t.kernel ξ η * φ η)).sum + d.regular ξ η * φ η = κ ξ η * φ η
  rw [d.eq_off_diagonal ξ η hηξ.symm, List.sum_map_mul_right]
  ring

end RothschildStein.P1.LiftedChart
