-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformSharpRows
public import RothschildStein.P1.ActualKernelRadialRows
public import RothschildStein.P1.PositivePrincipalUniformTruncationError
public import RothschildStein.P1.CriticalPrincipalUniformTruncationError
public import RothschildStein.P1.RegularUniformTruncationError

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

/-- Uniform sharp row data for an actual principal
component, including the critical endpoint. -/
def principalInput_uniformSharpRows (hF : C.IsStandardFrame F H K hQ)
    (t : PrincipalTerm F) (hd : t.degree ≤ 2) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLV : L ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    UniformSharpRows L F.rho (fun ξ η => t.kernel ξ η * φ η) where
  value := fun ξ => limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ =>
    ∫ η in {η | ε < F.rho ξ η}, t.kernel ξ η * φ η)
  integrable := by
    intro ξ hξ ε hε
    have D := C.principalInput_radialSharpRowData hF t hd φ (hLV hξ)
    simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using D.sharp_integrable ε hε
  limit := by
    intro ξ hξ
    have ht := (C.principalInput_radialSharpRowData hF t hd φ (hLV hξ)).sharp_limit
    simp only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq]
    rw [ht.limUnder_eq]
    exact ht
  error := by
    by_cases he : t.degree = 2
    · exact C.exists_criticalPrincipal_uniform_truncation_error_bound hF t he φ hL hLV
    · obtain ⟨r, A, hr, hA, hb⟩ :=
        C.exists_positivePrincipal_uniform_truncation_error_bound hF.lifted t
          (by omega) H.norm.gauge φ hL hLV
      refine ⟨r, A, hr, hA, ?_⟩
      intro ξ hξ ε hε hεr
      simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using
        hb ξ hξ ε hε hεr.le

/-- Uniform sharp row data for the actual regular
component of a decomposition with one derivative. -/
def regularInput_uniformSharpRows (hF : C.IsStandardFrame F H K hQ)
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLV : L ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    UniformSharpRows L F.rho (fun ξ η => r ξ η * φ η) where
  value := fun ξ => limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ =>
    ∫ η in {η | ε < F.rho ξ η}, r ξ η * φ η)
  integrable := by
    intro ξ hξ ε hε
    have D := C.regularInput_radialSharpRowData hF hr φ (hLV hξ)
    simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using D.sharp_integrable ε hε
  limit := by
    intro ξ hξ
    have ht := (C.regularInput_radialSharpRowData hF hr φ (hLV hξ)).sharp_limit
    simp only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq]
    rw [ht.limUnder_eq]
    exact ht
  error := by
    obtain ⟨ρ, A, hρ, hA, hb⟩ := C.exists_regular_uniform_truncation_error_bound
      hF.lifted hr H.norm.gauge φ hL hLV
    refine ⟨ρ, A, hρ, hA, ?_⟩
    intro ξ hξ ε hε hερ
    simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using hb ξ hξ ε hε hερ.le

/-- Actual type-zero kernels have uniform sharp
row convergence on every compact interior patch. Diagonal values are
removed only by almost everywhere equality. -/
def typeZeroInput_uniformSharpRows (hF : C.IsStandardFrame F H K hQ)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F 0 κ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLV : L ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    UniformSharpRows L F.rho (fun ξ η => κ ξ η * φ η) := by
  let rsUniformSharpFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let d : TypeDecomposition F 0 1 κ := Classical.choice (hκ 1)
  let DP := UniformSharpRows.listSum d.principal (fun t ξ η => t.kernel ξ η * φ η)
    (fun t ht => C.principalInput_uniformSharpRows hF t
      (by simpa using d.principal_degree t ht) φ hL hLV)
  let DR := C.regularInput_uniformSharpRows hF d.regular_isRegular φ hL hLV
  apply (DP.add DR).congr_ae
  intro ξ _
  filter_upwards [volume.ae_ne ξ] with η hηξ
  change (d.principal.map (fun t => t.kernel ξ η * φ η)).sum + d.regular ξ η * φ η = κ ξ η * φ η
  rw [d.eq_off_diagonal ξ η hηξ.symm, List.sum_map_mul_right]
  ring

end RothschildStein.P1.LiftedChart
