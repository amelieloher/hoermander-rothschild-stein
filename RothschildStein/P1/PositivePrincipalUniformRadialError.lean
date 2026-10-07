-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PositivePrincipalAbsoluteSmallBall
public import RothschildStein.P1.InputFamilyUniformRadialError
public import RothschildStein.P1.UniformLinearErrorLimit
public import RothschildStein.P1.PrincipalRowIntegrability

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

/-- Positive principal rows have uniform O(ε) convergence of the actual
whole smooth radial truncations on compact subsets of the chart. -/
theorem exists_positivePrincipal_uniform_radialError_bound
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (hd : t.degree ≤ 1)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖(∫ η, (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
        (t.kernel ξ η * φ η)) - (∫ η, t.kernel ξ η * φ η)‖ ≤ A * ε := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
  obtain ⟨r, A, hr, hA, hb⟩ :=
    C.exists_positivePrincipal_uniform_absoluteSmallBall_bound hF t hd hν ψ hL hLU
  have hi : ∀ ξ ∈ L, Integrable (fun η => t.cutoffModelKernel ξ η (C.Θ η ξ) * ψ η) := by
    intro ξ _
    have hrow := C.integrable_principal_row F hF.G_eq hF.Θ_eq hVU t hd
      (hF.pole_smooth t.star) (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star) ξ
    have hM := Classical.choose_spec
      (φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous)
    have hi := hrow.mul_bdd φ.contDiff.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    simpa only [PrincipalTerm.kernel_eq_cutoffModelKernel, hF.Θ_eq, ψ, TestFunction.coe_mk] using hi
  refine ⟨r / 2, 2 * A, by positivity, by positivity, ?_⟩
  intro ξ hξ ε hε hεr
  simpa only [PrincipalTerm.kernel_eq_cutoffModelKernel, hF.Θ_eq, ψ, TestFunction.coe_mk] using
    C.inputFamily_uniform_radialError_of_absoluteSmallBall hν t.cutoffModelKernel ψ
      hLU hi hb ξ hξ ε hε (by linarith)

/-- Actual smooth radial operator rows converge
uniformly on compact center sets. -/
theorem tendstoUniformlyOn_positivePrincipal_radialIntegral
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (hd : t.degree ≤ 1)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) :
    TendstoUniformlyOn (fun ε : ℝ => fun ξ => ∫ η,
      (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
        (t.kernel ξ η * φ η)) (fun ξ => ∫ η, t.kernel ξ η * φ η)
      (𝓝[>] (0 : ℝ)) L := by
  obtain ⟨radius, A, hRadius, _, hb⟩ :=
    C.exists_positivePrincipal_uniform_radialError_bound hF t hd hν φ hL hLU
  exact tendstoUniformlyOn_of_linearError hRadius hb

end RothschildStein.P1.LiftedChart
