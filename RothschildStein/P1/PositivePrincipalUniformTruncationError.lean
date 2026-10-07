-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PositivePrincipalUniformSmallBall
public import RothschildStein.P1.IntegrableFamilyUniformTruncation
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

/-- Positive principal rows have uniform prescribed
sharp-truncation convergence on compact subsets of a lifted frame. -/
theorem exists_positivePrincipal_uniform_truncation_error_bound
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (hd : t.degree ≤ 1)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLV : L ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ‖(∫ η in {η | ε < ν (C.Θ η ξ)}, t.kernel ξ η * φ η) -
        limUnder (𝓝[>] (0 : ℝ)) (fun δ : ℝ =>
          ∫ η in {η | δ < ν (C.Θ η ξ)}, t.kernel ξ η * φ η)‖ ≤ A * ε := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
  obtain ⟨r, A, hr, hA, hb⟩ :=
    C.exists_positivePrincipal_uniform_smallBall_bound hF t hd hν ψ hL (hLV.trans hVU)
  have hi : ∀ ξ ∈ L, Integrable (fun η => t.cutoffModelKernel ξ η (C.Θ η ξ) * ψ η) := by
    intro ξ _
    have hrow := C.integrable_principal_row F hF.G_eq hF.Θ_eq hVU t hd
      (hF.pole_smooth t.star) (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star) ξ
    have hM := Classical.choose_spec
      (φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous)
    have hi := hrow.mul_bdd φ.contDiff.continuous.aestronglyMeasurable (Eventually.of_forall hM)
    simpa only [PrincipalTerm.kernel_eq_cutoffModelKernel, hF.Θ_eq, ψ, TestFunction.coe_mk] using hi
  refine ⟨r, A, hr, hA, ?_⟩
  simpa only [PrincipalTerm.kernel_eq_cutoffModelKernel, hF.Θ_eq, ψ, TestFunction.coe_mk] using
    C.integrableFamily_uniform_truncation_error hν t.cutoffModelKernel ψ
      (hLV.trans hVU) hi hb

end RothschildStein.P1.LiftedChart
